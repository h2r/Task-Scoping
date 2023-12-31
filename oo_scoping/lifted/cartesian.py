from __future__ import annotations
import itertools
from dataclasses import dataclass
from typing import List, TypeVar, Tuple
from oo_scoping.lifted.abstract_groundings import (
    OperatorWithGroundingsSet,
    PVarGroundedSet,
)

# from pddl.logic import Constant, Variable
# from pddl.action import Action
# from pddl.parser.domain import Domain, DomainParser
# from pddl.parser.problem import Problem, ProblemParser

# from oo_scoping.test.domains.pickup_unlock_open import PickupUnlockOpenPaths
# from oo_scoping.examples.paths import Minecraft3Paths
from oo_scoping.action import Action
from typing import TypeAlias, Any, Dict, Iterable, Callable
import enum
import copy
from collections import defaultdict

# TODO: Make hashing/eq checking based on frozensets, order independent

# TODO: Use types from our PDDL parsers
Constant: TypeAlias = Any
Variable: TypeAlias = Any
# Action: TypeAlias = Any

PvarName: TypeAlias = str
EffectId: TypeAlias = str
"""ID to distinguish effects on the same variable.
We don't need to parse what the effect actually does, we just need to distinguish
distinct effects for the sake of partitioning skills by their effects.
"""

ParamName: TypeAlias = str
ObjectName: TypeAlias = str


@dataclass
class SingleGrounding:
    param_to_object: Dict[ParamName, ObjectName]


@dataclass(frozen=True, eq=True)
class CartesianGroundings:
    """Represents a set of groundings as a product of (groundings for v) for a set of variables v"""

    param_to_groundings: dict[ParamName, list[ObjectName]]

    def to_list_of_groundings(self) -> list[SingleGrounding]:
        """Get a list of all groundings."""
        return do_cartesian(self.param_to_groundings, SingleGrounding)

    def union(self, other: CartesianGroundings) -> CartesianGroundings:
        combined_variable_to_groundings = copy.deepcopy(self.param_to_groundings)
        for var_name, other_groundings in other.param_to_groundings.items():
            if var_name in combined_variable_to_groundings:
                combined_variable_to_groundings[
                    var_name
                ] = concatenate_without_dupes_inorder(
                    combined_variable_to_groundings[var_name], other_groundings
                )
            else:
                combined_variable_to_groundings[var_name] = copy.deepcopy(
                    other_groundings
                )
        return CartesianGroundings(combined_variable_to_groundings)

    def intersect(self, other: CartesianGroundings) -> CartesianGroundings:
        """We maybe don't need this"""
        intersected_variable_to_groundings: dict[ParamName, list[ObjectName]] = dict()
        for param_name, object_names in self.param_to_groundings.items():
            if param_name in other.param_to_groundings.keys():
                other_object_names = other.param_to_groundings[param_name]
                intersected_variable_to_groundings[param_name] = [
                    object_name
                    for object_name in object_names
                    if object_name in other_object_names
                ]
        return CartesianGroundings(intersected_variable_to_groundings)

    def relative_complement(self, other: CartesianGroundings) -> CartesianGroundings:
        """Return a CartesianGroundings that contains all groundings in self but _not_ in other."""
        filtered_param_to_groundings: dict[ParamName, list[ObjectName]] = dict()
        for param_name, object_names in self.param_to_groundings.items():
            banned_objects = other.param_to_groundings.get(param_name, [])
            filtered_param_to_groundings[param_name] = [
                obj for obj in object_names if obj not in banned_objects
            ]
        return CartesianGroundings(filtered_param_to_groundings)

    def __hash__(self) -> int:
        return hash(frozenset(self.param_to_groundings.items()))


class PvarDomain(enum.Enum):
    """What values can a pvar take."""

    binary = enum.auto()
    real = enum.auto()


@dataclass
class CartesianPvar:
    """A single pvar and a collection of groundings for it."""

    var_name: PvarName
    groundings: CartesianGroundings
    # domain: PvarDomain


PartialStateType: TypeAlias = Dict[CartesianPvar, int]
GoalType: TypeAlias = PartialStateType
"""For now assume a goal is a single value for a single grounding."""


@dataclass
class UngroundedPvar:
    """Pvar, with free variables for its arguments.
    This should likely be a parent class to CartesianPvar.
    """

    var_name: PvarName
    params: List[ParamName]


@dataclass(eq=True, frozen=True)
class CartesianPvarSet(PVarGroundedSet[PartialStateType, PartialStateType]):
    # pvars: List[CartesianPvar]
    name_to_groundings: Dict[PvarName, CartesianGroundings]

    @classmethod
    def new_empty(cls) -> CartesianPvarSet:
        return CartesianPvarSet(dict())

    @classmethod
    def from_concrete_variable_value_assignment(
        cls, cvva: GoalType
    ) -> CartesianPvarSet:
        """WLOG there is a single, grounded, goal pvar, so we just need to store that grounded pvar."""
        return CartesianPvarSet(
            {pvar.var_name: pvar.groundings for pvar in cvva.keys()}
        )

    def union(self, other: CartesianPvarSet) -> CartesianPvarSet:
        merged_name_to_groundings = copy.deepcopy(self.name_to_groundings)
        for pvar_name, other_groundings in other.name_to_groundings.items():
            if pvar_name not in merged_name_to_groundings.keys():
                merged_name_to_groundings[pvar_name] = copy.deepcopy(other_groundings)
            else:
                merged_name_to_groundings[pvar_name] = merged_name_to_groundings[
                    pvar_name
                ].union(other_groundings)
        return CartesianPvarSet(merged_name_to_groundings)

    def mask_from_partial_state(
        self, partial_state: PartialStateType
    ) -> PartialStateType:
        """Return a new partial state with these grounded PVars ignored"""
        masked_partial_state: PartialStateType = dict()
        for cartesian_pvar, val in partial_state.items():
            our_groundings = self.name_to_groundings.get(cartesian_pvar.var_name, None)
            if our_groundings is not None:
                # We hold some groundings of the lifted pvar. We must mask those from the output.
                masked_pvar = CartesianPvar(
                    cartesian_pvar.var_name,
                    cartesian_pvar.groundings.relative_complement(our_groundings),
                )
                masked_partial_state[masked_pvar] = val
            else:
                # We don't hold the lifted pvar at all, so we preserve the state entirely
                masked_partial_state[copy.deepcopy(cartesian_pvar)] = val
        return masked_partial_state

    def __hash__(self) -> int:
        return hash(frozenset(self.name_to_groundings.items()))

    def __eq__(self, __value: object) -> bool:
        if isinstance(__value, CartesianPvarSet):
            return frozenset(self.name_to_groundings.items()) == frozenset(
                __value.name_to_groundings.items()
            )
        else:
            return False


ActionName: TypeAlias = str


@dataclass(frozen=True, eq=True)
class UngroundedSingleVarEffect:
    """Effect on a single pvar. Needs to have free variables for the objects mentioned.
    The groundings for these free will be stored in the action holding this effect.

    Must be hashable and support equality checking. (We can get these for free via dataclass,
    as long as this class's attributes are all hashable and support equality, and we keep instances
     of this class immutable.)

    Does _not_ need to actually keep track of detailed effects. It needs
    """

    pvar: UngroundedPvar
    effect_id: EffectId

    def get_affected_lifted_pvars(self) -> List[UngroundedPvar]:
        raise NotImplementedError(
            "We need to define the data held by this class first."
        )


@dataclass(frozen=True, eq=True)
class UngroundedMultiVarEffect:
    pvar_to_effect: Dict[UngroundedPvar, UngroundedSingleVarEffect]


@dataclass(frozen=True, eq=True)
class UngroundedPrecondition:
    """Needs integration with logic tool. How we actually store the data in this class
    will most likely depend on the tool. Eg. for Z3 we use a z3.BoolRef.
    But we can't use Z3 for this, since it can't express lifted (ie first order logic) expressions.
    """

    pass


@dataclass(frozen=True, eq=True)
class CartesianPrecondition:
    """Needs integration with logic tool"""

    precondition: UngroundedPrecondition
    groundings: CartesianGroundings


@dataclass(eq=True, frozen=True)
class CartesianEffect:
    """Effect on a single pvar, using cartesian groundings."""

    var: UngroundedPvar
    effect_id: EffectId
    groundings: CartesianGroundings


@dataclass(eq=True, frozen=True)
class CartesianEffectSet:
    var_to_effect: Dict[PvarName, CartesianEffect]
    # effects: frozenset[CartesianEffect]


@dataclass(eq=True, frozen=True)
class CartesianGroundedAction:
    # TODO: Refactor/change this. It probably doesn't hold what we want how we want it.
    # Be mindful of how we track groundings and parameters (the things that determine how we affect the affected variable)
    name: ActionName
    parameters: List[UngroundedPvar]
    """Affect how the target variables are affected. Has variable names and types, but not groundings."""
    effects: CartesianEffectSet
    """Effects hold pvar, effect_id, and groundings. We store groundings separately for each effect so that
    we can remove irrelevant groundings for each pvar, based on relevant_pvars."""
    precondition: CartesianPrecondition
    """NOT just a partial state. Should keep track of the variable names/types. Also keeps track of groundings for now,
    because maybe the logic tool can prune grounding sets for quantified variables (ie variables not part of action.groundings).
    Also, it's possible that a parameter to the action is not mentioned in the precondition.

    Ideally we'll store an AST or something. The final form of this will depend on the logic tool we use
    (unless we just convert it to logic as needed). For now, we just need to be able to get UngroundedPvars from it,
    with object variable names.
    """
    groundings: CartesianGroundings
    """Groundings used for preconditions and parameters. effects use separate groundings for each pvar, though any of those
    grounding sets could just be a reference to this action-level groundings.
    TODO: Precondition can maybe use different groundings, in case the logic tool throws some away?"""

    def get_affected_pvars(self) -> CartesianPvarSet:
        raise NotImplementedError()

    def get_affected_relevant_pvars(
        self, relevant_pvars: CartesianPvarSet
    ) -> CartesianPvarSet:
        name_to_groundings: Dict[PvarName, CartesianGroundings] = dict()
        for pvar in self.effects.var_to_effect.keys():
            relevant_groundings = relevant_pvars.name_to_groundings.get(pvar, None)
            if relevant_groundings is not None:
                name_to_groundings[pvar] = self.groundings.intersect(
                    relevant_groundings
                )
        return CartesianPvarSet(name_to_groundings)

    def get_relevant_effects(
        self, relevant_pvars: CartesianPvarSet
    ) -> CartesianEffectSet:
        # TODO: Probably iterate over relevant_pvars instead. We iterate over effects for now
        name_to_effect: Dict[PvarName, CartesianEffect] = dict()
        for pvar, effect in self.effects.var_to_effect.items():
            relevant_groundings = relevant_pvars.name_to_groundings.get(pvar, None)
            if relevant_groundings is not None:
                filtered_groundings = self.groundings.intersect(relevant_groundings)
                name_to_effect[pvar] = CartesianEffect(
                    effect.var, effect.effect_id, filtered_groundings
                )
        return CartesianEffectSet(name_to_effect)


@dataclass
class CartesianGroundedActionsSet(
    OperatorWithGroundingsSet[
        CartesianPvarSet, PartialStateType, UngroundedMultiVarEffect
    ]
):
    actions: List[CartesianGroundedAction]

    def get_affected_pvars(self) -> CartesianPvarSet:
        pvars = CartesianPvarSet.new_empty()
        for a in self.actions:
            pvars = pvars.union(a.get_affected_pvars())
        return pvars

    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: PartialStateType
    ) -> CartesianPvarSet:
        """Requires a logic tool."""
        raise NotImplementedError()

    def partition_by_effects(
        self, relevant_pvars: CartesianPvarSet
    ) -> Dict[CartesianEffectSet, CartesianGroundedActionsSet]:
        """Group operators by their effects on relevant variables.

        Make sure to keep track of groundings for operator params, and groundings
        for quantifiers separately. (IDK if we need this warning here or for merge)
        No logic tool needed.

        A first version of this will treat ungrounded effects as the same only if they use
        the same names for their object variables. We aren't going to deal with object variable
        renaming/symmetry stuff.

        # TODO: I think this may be throwing out too much information about groundings for the new operators.
        Make sure it isn't.
        """
        effects_to_actions: Dict[
            CartesianEffectSet, List[CartesianGroundedAction]
        ] = defaultdict(list)
        for action in self.actions:
            effects_to_actions[action.get_relevant_effects(relevant_pvars)].append(
                action
            )
        return {
            effect: CartesianGroundedActionsSet(actions)
            for effect, actions in effects_to_actions.items()
        }

    def get_joined_names(self) -> str:
        """Concatenates all action names. Used to create names for merged actions."""
        return "|".join([a.name for a in self.actions])

    def get_all_parameters(self) -> List[UngroundedPvar]:
        """Get parameters used in any action."""
        all_params: List[UngroundedPvar] = []
        for a in self.actions:
            all_params = concatenate_without_dupes_inorder(all_params, a.parameters)
        return all_params

    def get_merged_groundings(self) -> CartesianGroundings:
        # TODO: What are the new groundings?
        raise NotImplementedError(
            "What should this be? I think not just intersection or union. Think it through"
            " based on what happens in og enumerated scoping."
        )

    def merge_operators_with_matching_effects(
        self,
        initial_state: PartialStateType,
        effects_to_operators: Dict[CartesianEffectSet, CartesianGroundedActionsSet],
    ) -> CartesianGroundedActionsSet:
        """Merge operators which have the same effects on relevant variables. initial_state is used to simplify preconditions.

        Requires a logic tool. This is probably the hardest thing to implement.
        """
        merged_actions: List[CartesianGroundedAction] = []
        for effects, actions in effects_to_operators.items():
            # TODO: Refactor abstract method based on the decomposition used here. Probably.
            merged_actions.append(
                CartesianGroundedAction(
                    name=actions.get_joined_names(),
                    parameters=actions.get_all_parameters(),
                    precondition=actions.merge_preconditions(initial_state),
                    groundings=actions.get_merged_groundings(),
                    effects=effects,
                )
            )
        raise NotImplementedError()

    def merge_preconditions(
        self, initial_state: PartialStateType
    ) -> CartesianPrecondition:
        # TODO: Implement
        raise NotImplementedError("This depends on the logic tool we use.")


"""This got too fancy with passing in a callable. We should probably inline it."""
K = TypeVar("K")
V = TypeVar("V")
R = TypeVar("R")


def identity(x: R) -> R:
    return x


def do_cartesian(
    d: dict[K, list[V]], f: Callable[[dict[K, V]], R] = identity
) -> list[R]:
    """
    Args:
        d: A dict mapping each key to a list of candidate values

    Returns:
        A list of all possible (key -> value) mappings.
    """
    new_lists: list[R] = []
    # This relies on values and keys being synced. This should be true
    # in standard python, but may break on other variants of python, since
    # dicts being ordered is an implementation detail.
    keys = list(d.keys())
    vals_product = itertools.product(*d.values())
    for assigment_tuple in vals_product:
        assigment_tuple: tuple[V, ...]
        # TODO remove assert for speedup
        assert len(keys) == len(assigment_tuple)
        new_dict = {keys[i]: assigment_tuple[i] for i in range(len(keys))}
        new_lists.append(f(new_dict))
    return new_lists


def concatenate_without_dupes_inorder(arr0: Iterable[V], arr1: Iterable[V]) -> List[V]:
    # TODO: Don't use this, especially when concatenating many iterables at once. Do something faster.
    new_list: List[V] = copy.copy(list(arr0))
    for x in arr1:
        if x not in new_list:
            new_list.append(x)
    return new_list


if __name__ == "__main__":
    pass
