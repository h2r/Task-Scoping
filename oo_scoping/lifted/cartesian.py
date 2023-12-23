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
from typing import TypeAlias, Any, Dict, Iterable
import enum
import copy


# TODO: Use types from our PDDL parsers
Constant: TypeAlias = Any
Variable: TypeAlias = Any
# Action: TypeAlias = Any

@dataclass
class CartesianGroundings:
    """Represents a set of groundings as a product of (groundings for v) for a set of variables v"""
    variable_to_groundings: dict[Variable, list[Constant]]

    def to_list_of_groundings(self) -> list[dict[Variable, Constant]]:
        """Get a list of all groundings."""
        return do_cartesian(self.variable_to_groundings)

class PvarDomain(enum.Enum):
    """What values can a pvar take."""
    binary = enum.auto()
    real = enum.auto()

@dataclass
class CartesianPvar:
    var_name: str
    groundings: CartesianGroundings
    domain: PvarDomain

PartialStateType: TypeAlias = Dict[CartesianPvar, int]

@dataclass(eq=True, frozen=True)
class EffectSingleVar:
    # TODO: Should this even be a cartesian pvar? Or just lifted pvar name? I'm not sure.
    pvar: CartesianPvar
    # TODO: Use some encoding for effect val. Probably from the pddl parser directly.
    effect_val: str

@dataclass(eq=True, frozen=True)
class EffectsMultiVar:
    # TODO: Probably wrong, needs to be more tightly integrated into actions.
    """Effects on a multiple of pvars. Each action has one of these."""
    effects: List[EffectSingleVar]



@dataclass(eq=True, frozen=True)
class CartesianPvarSet(PVarGroundedSet[PartialStateType, PartialStateType]):
    pvars: List[CartesianPvar]

    @classmethod
    def new_empty(cls) -> CartesianPvarSet:
        return CartesianPvarSet([])

    @classmethod
    def from_concrete_variable_value_assignment(cls, cvva: PartialStateType) -> CartesianPvarSet:
        return CartesianPvarSet(list(cvva.keys()))

    def union(self, other: CartesianPvarSet) -> CartesianPvarSet:
        return CartesianPvarSet(concatenate_without_dupes_inorder(self.pvars, other.pvars))

    def mask_from_partial_state(
        self, partial_state: PartialStateType
    ) -> PartialStateType:
        """Return a new partial state with these grounded PVars ignored"""
        return {pvar: val for pvar, val in partial_state.items() if pvar not in self.pvars}
    


    
@dataclass(eq=True, frozen=True)
class CartesianGroundedAction:
    action: Action
    groundings: CartesianGroundings

    def assert_groundings(self) -> None:
        """Raise an error if we the groundings are missing some variables"""
        raise NotImplementedError()
    

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



K = TypeVar("K")
V = TypeVar("V")
def do_cartesian(d: dict[K, list[V]]) -> list[dict[K, V]]:
    """
    Args:
        d: A dict mapping each key to a list of candidate values
        
    Returns:
        A list of all possible (key -> value) mappings.
    """
    new_lists: list[dict[K, V]] = []
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
        new_lists.append(new_dict)
    return new_lists


def concatenate_without_dupes_inorder(arr0: Iterable[V], arr1: Iterable[V]) -> List[V]:
    new_list: List[V] = copy.copy(list(arr0))
    for x in arr1:
        if x not in new_list:
            new_list.append(x)
    return new_list

if __name__ == "__main__":
    pass