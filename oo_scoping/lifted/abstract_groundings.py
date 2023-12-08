"""Base classes for scoping objects. We subclass these with concrete implementations."""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, TypeVar, Type, Generic
from abc import ABC, abstractmethod, abstractclassmethod
from oo_scoping.lifted.atomic_classes import *


PVGS = TypeVar("PVGS")
GoalType = TypeVar("GoalType")
PartialStateType = TypeVar("PartialStateType")


class PVarGroundedSet(Generic[GoalType, PartialStateType], ABC):
    """Set of grounded PVars. Probably using some smarted encoding than enumeration.
    
    Each subclass needs to
    
    1. Store a set of grounded PVars. 
        The simplest way is a list of grounded pvars. Ideally you should use more compact representations.
    2. Implement the methods below.
    """

    pass

    @classmethod
    def new_empty(cls: Type[PVGS]) -> PVGS:
        raise NotImplementedError()

    @classmethod
    def from_concrete_variable_value_assignment(
        cls: Type[PVGS], cvva: GoalType
    ) -> PVGS:
        raise NotImplementedError()

    @classmethod
    def union(cls: Type[PVGS], grounded_sets: List[PVGS]) -> PVGS:
        raise NotImplementedError()

    @abstractmethod
    def mask_from_partial_state(self, partial_state: PartialStateType) -> PartialStateType:
        """Return a new partial state with these grounded PVars ignores"""
        raise NotImplementedError()


OWGS = TypeVar("OWGS")


class OperatorWithGroundingsSet(Generic[PVGS, PartialStateType], ABC):
    """Collection of operators with groundings.


    The simplest implementation is just a List[OperatorWithGroundings]
    We have a class for this, rather than just using a list, because we may be able to compress/amortize
    some data/compute this way.
    """

    @abstractmethod
    def get_affected_pvars(self) -> PVGS:
        raise NotImplementedError()

    @abstractmethod
    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: PartialStateType
    ) -> PVGS:
        """Maybe hard."""
        # TODO: Possibly the input should be something else with more structure, that lets us be more efficient.
        raise NotImplementedError()

    @abstractmethod
    def get_merged_operators(
        self: OWGS, initial_state: PartialStateType, relevant_pvars: PVGS
    ) -> OWGS:
        """This is probably the hardest thing to implement.
        Make sure to keep track of groundings for operator params, and groundings
        for quantifiers separately.

        Also: how do we cope with the initial_state when without grounding everything?
        """
        raise NotImplementedError("Child class should implement this")

OperatorCollectionType = TypeVar("OperatorCollectionType", bound=OperatorWithGroundingsSet)


PDDLTaskTypeVar = TypeVar("PDDLTaskTypeVar")

class PDDLTask(Generic[PVGS, GoalType, PartialStateType, OperatorCollectionType], ABC):
    """Holds a PDDL Task. Main thing passed into scoping probably. Needs to implement parsing."""
    all_operators: OperatorCollectionType
    initial_state: PartialStateType
    goal: GoalType

    @classmethod
    def from_domain_and_problem_files(cls: Type[PDDLTaskTypeVar], domain_path: str, problem_path: str) -> PDDLTaskTypeVar:
        raise NotImplementedError("Child classes should implement this")
