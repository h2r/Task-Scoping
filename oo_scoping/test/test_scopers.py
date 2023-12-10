import unittest
from typing import Generic, Iterable, TypeVar

from oo_scoping.lifted.enumerated_operators_like_og_scoping import EnumeratedPDDLTask
from oo_scoping.PDDLz3 import PDDL_Parser_z3
from oo_scoping.scoping import scope
from oo_scoping.skill_classes import SkillPDDL
from oo_scoping.test.domains.pickup_unlock_open import PickupUnlockOpenPaths
from oo_scoping.test.domains.radio import RadioPaths
from oo_scoping.test.domains.double_doors import DoubleDoorsPaths
from oo_scoping.z3_type_aliases import Z3Variable

# Scoper = Callable[[str, str]]


class TestHolder:
    """This outer-class just hides the test definitions from pytest discovery."""

    class ScopingTestDefinitions(unittest.TestCase):
        """Define scoping tests. The general organization of each test will be:

        1. Specify domain and problem paths
        2. Make some asserts about the scoped result.

        This base class is agnostic to what scoper is used, as long as it can
        read PDDL and return some yet-to-be-determined common format.

        Common format will probably be a list of `SkillPDDL` and/or relevant grounded z3 pvars for now,
        since thats what our current scopers can use. We'll abstract it out later as needed.
        """

        def get_relevant_operators_and_pvars(
            self, domain_path: str, problem_path: str
        ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
            """Get relevant grounded operators and pvars. For now we use list-of grounded
            representation.
            If we add tests for large domains, we'll need to allow lifted representations.
            """
            raise NotImplementedError("A child class should define this.")

        def get_all_operators_and_pvars(
            self, domain_path: str, problem_path: str
        ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
            """Get all grounded operators and pvars. For now we use list-of grounded
            representation.
            If we add tests for large domains, we'll need to allow lifted representations.
            """
            raise NotImplementedError("A child class should define this.")

        def test_pickup_unlock_open_everything_is_relevant(self) -> None:
            """For the pickup -> unlock -> open domain: if we have no key, door is closed and locked, all vars are relevant."""
            _scoped_operators, scoped_pvars = self.get_relevant_operators_and_pvars(
                PickupUnlockOpenPaths.domain, PickupUnlockOpenPaths.Problems.initial
            )
            _og_operators, og_pvars = self.get_all_operators_and_pvars(
                PickupUnlockOpenPaths.domain, PickupUnlockOpenPaths.Problems.initial
            )
            # We shouldn't scope out anything. For now, we'll just assert the pvar names match
            venn = Venn(
                set(map(str, og_pvars)),
                set(map(str, scoped_pvars)),
                ignored_values=["dummy_goal"],
            )
            print(venn)

            self.assertTrue(venn.match(), f"{venn}")

        def test_pickup_unlock_open_already_unlocked(self) -> None:
            """For the pickup -> unlock -> open domain: if the door is already unlocked, then the only relevant var is open."""
            _scoped_operators, scoped_pvars = self.get_relevant_operators_and_pvars(
                PickupUnlockOpenPaths.domain,
                PickupUnlockOpenPaths.Problems.door_is_unlocked,
            )
            # We shouldn't scope out anything. For now, we'll just assert the pvar names match
            correct_var_names = ["is-open(d)"]
            venn = Venn(
                correct_var_names,
                set(map(str, scoped_pvars)),
                ignored_values=["dummy_goal"],
            )
            self.assertTrue(venn.match(), f"{venn}")

        def test_radio(self) -> None:
            """We need to open the door. The radio is never conditioned on, so it's trivially irrelevant."""
            _scoped_operators, scoped_pvars = self.get_relevant_operators_and_pvars(
                RadioPaths.domain, RadioPaths.Problems.initial
            )
            correct_var_names = ["is-open(d)"]
            venn = Venn(
                correct_var_names,
                set(map(str, scoped_pvars)),
                ignored_values=["dummy_goal"],
            )
            self.assertTrue(venn.match(), f"{venn}")


        def test_double_doors_operator_merge(self) -> None:
            """If we can enter through left or right door, we shouldn't care which door is open."""
            _scoped_operators, scoped_pvars = self.get_relevant_operators_and_pvars(
                DoubleDoorsPaths.domain, DoubleDoorsPaths.Problems.outside_left_open_no_key
            )
            correct_var_names = ["is-inside(d)"]
            venn = Venn(
                correct_var_names,
                set(map(str, scoped_pvars)),
                ignored_values=["dummy_goal"],
            )
            self.assertTrue(venn.match(), f"{venn}")
            pass


class TestLifedButNotReallyScoping(TestHolder.ScopingTestDefinitions):
    """Test that the refactored, but not really lifted, scoping works."""

    def get_relevant_operators_and_pvars(
        self, domain_path: str, problem_path: str
    ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
        task = EnumeratedPDDLTask.from_domain_and_problem_files(
            domain_path, problem_path
        )
        operators, vars = task.scope()
        return operators.operators_grounded, vars.pvars

    def get_all_operators_and_pvars(
        self, domain_path: str, problem_path: str
    ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
        """TODO: We get pvar string many times, instead of just once. Could be optimized."""
        task = EnumeratedPDDLTask.from_domain_and_problem_files(
            domain_path, problem_path
        )
        return task.all_operators.operators_grounded, task.all_pvars.pvars


class TestClassicScoping(TestHolder.ScopingTestDefinitions):
    """Test that classic scoping works."""

    def get_relevant_operators_and_pvars(
        self, domain_path: str, problem_path: str
    ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
        """Copied from scope_pddl"""
        parser = PDDL_Parser_z3()
        parser.parse_domain(domain_path)
        parser.parse_problem(problem_path)

        skill_list = parser.get_skills()

        # This below block converts all the domain's goals to z3
        goal_cond = parser.get_goal_cond()

        # This below block converts all the domain's initial conditions to z3
        init_cond_list = parser.get_init_cond_list()

        # Run the scoper on the constructed goal, skills and initial condition
        rel_pvars, _cl_pvars, rel_skills = scope(
            goals=goal_cond,
            skills=skill_list,
            start_condition=init_cond_list,
            verbose=0,
        )
        return rel_skills, rel_pvars

    def get_all_operators_and_pvars(
        self, domain_path: str, problem_path: str
    ) -> tuple[list[SkillPDDL], list[Z3Variable]]:
        parser = PDDL_Parser_z3()
        parser.parse_domain(domain_path)
        parser.parse_problem(problem_path)

        skill_list = parser.get_skills()

        # This below block converts all the domain's goals to z3
        str_to_var = parser.make_str2var_dict()
        pvars = list(str_to_var.values())
        return skill_list, pvars


def map_str(arr: list) -> list[str]:
    return [str(x) for x in arr]


T = TypeVar("T")


class Venn(Generic[T]):
    def __init__(
        self,
        left: Iterable[T],
        right: Iterable[T],
        ignored_values: Iterable[T] = tuple(),
    ) -> None:
        """This is inneficient since it loops multiple times. Could improve.
        Also could use custom equality checker, to simplify z3 stuff.
        """
        self.left = [x for x in left if x not in right and x not in ignored_values]
        self.both = [x for x in left if x in right and x not in ignored_values]
        self.right = [x for x in right if x not in left and x not in ignored_values]

    def match(self) -> bool:
        return len(self.left) == 0 and len(self.right) == 0

    def __repr__(self) -> str:
        return f"Venn({self.left} | {self.both} | {self.right})"


def empty_or_dummy(arr0: list[str]) -> bool:
    return arr0 == [] or arr0 == ["dummy_goal"]


# def eq_pvars(pvars0: list[Z3Variable], pvars1: list[Z3Variable], ignore_dummy: bool = True) -> bool:
#     if ignore_dummy
#     venn = Venn(map_str(pvars0), map_str(pvars1))


def scope_pddl_get_vars_and_skills(
    domain: str, problem: str
) -> tuple[list[Z3Variable], list[SkillPDDL]]:
    """Copied from scope_pddl"""
    parser = PDDL_Parser_z3()
    parser.parse_domain(domain)
    parser.parse_problem(problem)

    skill_list = parser.get_skills()

    # This below block converts all the domain's goals to z3
    goal_cond = parser.get_goal_cond()

    # This below block converts all the domain's initial conditions to z3
    init_cond_list = parser.get_init_cond_list()

    # Run the scoper on the constructed goal, skills and initial condition
    rel_pvars, cl_pvars, rel_skills = scope(
        goals=goal_cond, skills=skill_list, start_condition=init_cond_list, verbose=0
    )
    return rel_pvars, rel_skills
