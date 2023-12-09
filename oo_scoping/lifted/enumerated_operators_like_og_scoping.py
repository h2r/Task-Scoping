"""Data structures and methods for unlifted scoping."""
from __future__ import annotations

from dataclasses import dataclass
from functools import cached_property
from typing import List

import z3

from oo_scoping.lifted.abstract_groundings import (
    OperatorWithGroundingsSet,
    PDDLTask,
    PVarGroundedSet,
)
from oo_scoping.PDDLz3 import PDDL_Parser_z3
from oo_scoping.scoping import effects2pvars, skills2effects
from oo_scoping.skill_classes import SkillPDDL, merge_skills_pddl, EffectTypePDDL
from oo_scoping.utils import (
    get_atoms,
    get_unique_z3_vars,
    solver_implies_condition,
    split_conj,
)
from oo_scoping.z3_type_aliases import (
    Z3ValueAssignment,
    Z3ValueAssignmentList,
    Z3Variable,
)


@dataclass(frozen=True)
class ListOfPvarGrounded(PVarGroundedSet[Z3ValueAssignment, Z3ValueAssignmentList]):
    """Stores a list of grounded pvars, like OG scoping. No compression, completely unlifted."""

    pvars: List[Z3Variable]

    @classmethod
    def new_empty(cls) -> ListOfPvarGrounded:
        return ListOfPvarGrounded([])

    @classmethod
    def from_concrete_variable_value_assignment(
        cls, cvva: Z3ValueAssignment
    ) -> ListOfPvarGrounded:
        atom = get_atoms_assert_one(cvva)
        return ListOfPvarGrounded([atom])

    @classmethod
    def union(cls, grounded_sets: List[ListOfPvarGrounded]) -> ListOfPvarGrounded:
        pvars_with_duplicates: List[Z3Variable] = []
        for g in grounded_sets:
            pvars_with_duplicates += g.pvars
        pvars_without_duplicates = get_unique_z3_vars(pvars_with_duplicates)
        return ListOfPvarGrounded(pvars_without_duplicates)

    def mask_from_partial_state(
        self, partial_state: Z3ValueAssignmentList
    ) -> Z3ValueAssignmentList:
        """Return a new partial state with these grounded PVars ignores"""
        partial_state_masked: Z3ValueAssignmentList = []
        for value_assignment in partial_state:
            name = value_assignment_to_name(value_assignment)
            if name not in self.pvar_names:
                partial_state_masked.append(value_assignment)
        return partial_state_masked

    @cached_property
    def pvar_names(self) -> List[str]:
        """Get names of pvars."""
        return [str(p) for p in self.pvars]


def get_atoms_assert_one(expr: z3.ExprRef) -> z3.ExprRef:
    """Assert that expr has a single atom and return it."""
    atoms = get_atoms(expr)
    if len(atoms) != 1:
        raise ValueError(f"More than one atom: {expr}; {atoms}")
    return atoms[0]


def value_assignment_to_name(value_assignment: Z3ValueAssignment) -> str:
    # TODO?: Remove assert to get a speedup. Assert is here to make dev less buggy.
    atom = get_atoms_assert_one(value_assignment)
    return str(atom)


@dataclass
class ListOfOperatorGroundeds(
    OperatorWithGroundingsSet[ListOfPvarGrounded, Z3ValueAssignmentList]
):
    operators_grounded: List[SkillPDDL]
    solver: z3.Solver
    """We store a z3 solver becuase creating them is expensive."""

    def get_affected_pvars(self) -> ListOfPvarGrounded:
        effects = skills2effects(self.operators_grounded)
        pvars = effects2pvars(effects)
        return ListOfPvarGrounded(pvars)

    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: Z3ValueAssignmentList
    ) -> ListOfPvarGrounded:
        """
        Args:
            initial_state_guaranteed: The portion of the initial state that cannot be affected
                by any of our grounded operators.

        Returns:
            The pvars which we may need to affect.

        Overview of method:
            2. Convert each precondition into CNF
            3. Filter out clauses in the CNFs that are implied by initial_state_guaranteed
            4. Collect the pvars from the remaining clauses
            5. Add in any parameters from our operators

        An alternative implementation could be (I think):
            1. Simplify each precondition in the context of initial_state_guaranteed
            2. collect pvars from remaining conditions
            3. Add in any parameters from our operators
        This may be better suited to lifted variants.
        """

        # Add initial_state_guaranteed to the solver
        self.solver.push()
        self.solver.add(*initial_state_guaranteed)

        pvars_new: List[Z3Variable] = []
        for operator in self.operators_grounded:
            # Params are always relevant
            pvars_new.extend(operator.params)
            clauses = split_conj(operator.precondition)
            # We shouldn't need this assert. split_conj should _always_ return list[z3.ExprRef]
            assert isinstance(clauses, list)
            for clause in clauses:
                if not solver_implies_condition(self.solver, clause):
                    pvars_new.extend(get_atoms(clause))
        self.solver.pop()
        return ListOfPvarGrounded(pvars_new)

    def get_merged_operators(
        self, initial_state: Z3ValueAssignmentList, relevant_pvars: ListOfPvarGrounded
    ) -> ListOfOperatorGroundeds:
        """Partition operators by relevant_pvars and then merge them."""
        self.solver.push()
        self.solver.add(*initial_state)
        merged_operators = merge_skills_pddl(
            self.operators_grounded, relevant_pvars.pvars, self.solver
        )
        self.solver.pop()
        return ListOfOperatorGroundeds(merged_operators, self.solver)


@dataclass
class EnumeratedPDDLTask(
    PDDLTask[
        ListOfPvarGrounded,
        Z3ValueAssignment,
        Z3ValueAssignmentList,
        ListOfOperatorGroundeds,
    ]
):
    all_operators: ListOfOperatorGroundeds
    all_pvars: ListOfPvarGrounded
    initial_state: Z3ValueAssignmentList
    goal: Z3ValueAssignment
    """For now we're just making goal always the dummy_goal. We'll remove that later."""
    pvars_grounding_type = ListOfPvarGrounded

    @classmethod
    def from_domain_and_problem_files(
        cls, domain_path: str, problem_path: str
    ) -> EnumeratedPDDLTask:
        parser = PDDL_Parser_z3()
        parser.parse_domain(domain_path)
        parser.parse_problem(problem_path)
        # TODO: Handle dummy goal stuff. Store relevant data.

        skill_list = parser.get_skills()
        goal_cond = parser.get_goal_cond()
        initial_state = parser.get_init_cond_list()

        dummy_goal = z3.Bool(
            "dummy_goal"
        )  # TODO make sure this var does not already exist

        dummy_goal_et = EffectTypePDDL(dummy_goal, 0)
        dummy_final_skill = SkillPDDL(goal_cond, "DummyFinalSkill", dummy_goal_et)
        skills_with_dummy = skill_list + [dummy_final_skill]
        str_to_var = parser.make_str2var_dict()
        pvars = ListOfPvarGrounded(list(str_to_var.values()))
        return EnumeratedPDDLTask(
            ListOfOperatorGroundeds(skills_with_dummy, z3.Solver()),
            pvars,
            initial_state,
            dummy_goal,
        )
