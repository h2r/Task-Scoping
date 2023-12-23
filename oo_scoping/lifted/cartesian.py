from __future__ import annotations
import itertools
from dataclasses import dataclass
from typing import List, TypeVar
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

@dataclass
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
                combined_variable_to_groundings[var_name] = concatenate_without_dupes_inorder(combined_variable_to_groundings[var_name], other_groundings)
            else:
                combined_variable_to_groundings[var_name] = copy.deepcopy(other_groundings)
        return CartesianGroundings(combined_variable_to_groundings)
    
    def intersect(self, other: CartesianGroundings) -> CartesianGroundings:
        """We maybe don't need this"""
        intersected_variable_to_groundings: dict[ParamName, list[ObjectName]] = dict()
        for param_name, object_names in self.param_to_groundings.items():
            if param_name in other.param_to_groundings.keys():
                other_object_names = other.param_to_groundings[param_name]
                intersected_variable_to_groundings[param_name] = [object_name for object_name in object_names if object_name in other_object_names]
        return CartesianGroundings(intersected_variable_to_groundings)
    
    def relative_complement(self, other: CartesianGroundings) -> CartesianGroundings:
        """Return a CartesianGroundings that contains all groundings in self but _not_ in other."""
        filtered_param_to_groundings: dict[ParamName, list[ObjectName]] = dict()
        for param_name, object_names in self.param_to_groundings.items():
            banned_objects = other.param_to_groundings.get(param_name, [])
            filtered_param_to_groundings[param_name] = [obj for obj in object_names if obj not in banned_objects]
        return CartesianGroundings(filtered_param_to_groundings)
    
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

# @dataclass(eq=True, frozen=True)
# class EffectSingleVar:
#     pvar: PvarName
#     # TODO: Use some encoding for effect val. Probably from the pddl parser directly.
#     effect_val: str

@dataclass(eq=True, frozen=True)
class EffectsMultiVar:
    # TODO: Probably wrong, needs to be more tightly integrated into actions.
    """Effects on a multiple of pvars. Each action has one of these."""
    effects: Dict[PvarName, EffectId]



@dataclass(eq=True, frozen=True)
class CartesianPvarSet(PVarGroundedSet[PartialStateType, PartialStateType]):
    # pvars: List[CartesianPvar]
    name_to_groundings: Dict[PvarName, CartesianGroundings]

    @classmethod
    def new_empty(cls) -> CartesianPvarSet:
        return CartesianPvarSet(dict())

    @classmethod
    def from_concrete_variable_value_assignment(cls, cvva: GoalType) -> CartesianPvarSet:
        """WLOG there is a single, grounded, goal pvar, so we just need to store that grounded pvar."""
        return CartesianPvarSet({pvar.var_name: pvar.groundings for pvar in cvva.keys()})

    def union(self, other: CartesianPvarSet) -> CartesianPvarSet:
        merged_name_to_groundings = copy.deepcopy(self.name_to_groundings)
        for pvar_name, other_groundings in other.name_to_groundings.items():
            if pvar_name not in merged_name_to_groundings.keys():
                merged_name_to_groundings[pvar_name] = copy.deepcopy(other_groundings)
            else:
                merged_name_to_groundings[pvar_name] = merged_name_to_groundings[pvar_name].union(other_groundings)
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
                masked_pvar = CartesianPvar(cartesian_pvar.var_name, cartesian_pvar.groundings.relative_complement(our_groundings))
                masked_partial_state[masked_pvar] = val
            else:
                # We don't hold the lifted pvar at all, so we preserve the state entirely
                masked_partial_state[copy.deepcopy(cartesian_pvar)] = val
        return masked_partial_state
    


ActionName: TypeAlias = str

@dataclass(eq=True, frozen=True)
class CartesianGroundedAction:
    # TODO: Refactor/change this. It probably doesn't hold what we want how we want it.
    # Be mindful of how we track groundings and parameters (the things that determine how we affect the affected variable)
    name: ActionName
    parameters: Any
    """Affect how the target variables are affected. Has variable names and types, but not groundings."""
    effects: Any
    """Effects should keep track of the variable names/types it takes, but not groundings."""
    precondition: Any
    """NOT just a partial state. Should keep track of the variable names/types, but not groundings."""
    groundings: CartesianGroundings
    """We _probably_ want to store the groundings here, rather than in the effects/preconditions/parameters."""

@dataclass
class CartesianGroundedActionsSet(OperatorWithGroundingsSet[CartesianPvarSet, PartialStateType,EffectsMultiVar]):
    actions: List[CartesianGroundedAction]

    def get_affected_pvars(self) -> CartesianPvarSet:
        raise NotImplementedError()

    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: PartialStateType
    ) -> CartesianPvarSet:
        raise NotImplementedError()


    def partition_by_effects(self, relevant_pvars: CartesianPvarSet) -> Dict[EffectsMultiVar, CartesianGroundedActionsSet]:
        """Group operators by their effects on relevant variables.

        Make sure to keep track of groundings for operator params, and groundings
        for quantifiers separately. (IDK if we need this warning here or for merge)
        """
        raise NotImplementedError()

    def merge_operators_with_matching_effects(
        self,
        initial_state: PartialStateType,
        effects_to_operators: Dict[EffectsMultiVar, CartesianGroundedActionsSet],
    ) -> CartesianGroundedActionsSet:
        """Merge operators which have the same effects on relevant variables. initial_state is used to simplify preconditions.

        This is probably the hardest thing to implement.
        """
        raise NotImplementedError()



"""This got too fancy with passing in a callable. We should probably inline it."""
K = TypeVar("K")
V = TypeVar("V")
R = TypeVar("R")

def identity(x: R) -> R:
    return x

def do_cartesian(d: dict[K, list[V]], f: Callable[[dict[K, V]], R] = identity) -> list[R]:
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
    new_list: List[V] = copy.copy(list(arr0))
    for x in arr1:
        if x not in new_list:
            new_list.append(x)
    return new_list

if __name__ == "__main__":
    pass