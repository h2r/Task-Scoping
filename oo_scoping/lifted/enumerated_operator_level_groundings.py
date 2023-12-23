"""These are collection classes similar to current scoping, 
except that we group together concrete operators that come from the same lifted operator.
VERY NOT COMPLETE.

"""
from __future__ import annotations
from typing import List, TypeVar
from dataclasses import dataclass


from oo_scoping.lifted.abstract_groundings import OperatorWithGroundingsSet, PVarGroundedSet
from oo_scoping.lifted.atomic_classes import PVarWithGroundings, OperatorLifted, GroundingsSet, PartialState


@dataclass
class OperatorWithGroundings:
    """A single lifted operator, and a set of groundings."""

    operator_lifted: OperatorLifted
    groundings_set: GroundingsSet

    def get_affected_pvars(self) -> List[PVarWithGroundings]:
        raise NotImplementedError("TODO")


@dataclass
class ListOfPVarsWithGroundings(PVarGroundedSet):
    pvars_with_groundings: List[PVarWithGroundings]

    def mask_from_partial_state(self, partial_state: PartialState) -> PartialState:
        raise NotImplementedError("TODO")

class ListOfOperatorsWithGroundings(OperatorWithGroundingsSet):
    """Relatively straightforward implementation.
    In rust, maybe this itself would generic over OperatorWithGroundings.
    """

    operators_with_groundings: List[OperatorWithGroundings]

    def get_affected_pvars(self) -> PVarGroundedSet:
        # TODO: Clean this up. Use union.
        list_of_lists = [o.get_affected_pvars() for o in self.operators_with_groundings]
        vars =  concat_lists_without_duplicates(list_of_lists)
        return ListOfPVarsWithGroundings(vars)

    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: PartialState
    ) -> PVarGroundedSet:
        raise NotImplementedError()

    def get_merged_operators(
        self, initial_state: PartialState, relevant_pvars: PVarGroundedSet
    ) -> ListOfOperatorsWithGroundings:
        raise NotImplementedError()


T = TypeVar("T")

# TODO: Probably delete this.
def concat_lists_without_duplicates(list_of_lists: List[List[T]]) -> List[T]:
    new_list: List[T] = []
    for l in list_of_lists:
        l += new_list
    return list(set(new_list))
