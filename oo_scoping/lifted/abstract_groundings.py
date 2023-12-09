"""Base classes for scoping objects. We subclass these with concrete implementations.

The toplevel class is PDDLTask. All other classes exist to support PDDLTask.scope()."""
from __future__ import annotations

from abc import ABC, abstractmethod
from typing import Generic, List, Type, TypeVar


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
    def mask_from_partial_state(
        self, partial_state: PartialStateType
    ) -> PartialStateType:
        """Return a new partial state with these grounded PVars ignores"""
        raise NotImplementedError()

PVGSBound = TypeVar("PVGSBound", bound=PVarGroundedSet)

OWGS = TypeVar("OWGS")


class OperatorWithGroundingsSet(Generic[PVGSBound, PartialStateType], ABC):
    """Collection of operators with groundings.


    The simplest implementation is just a List[OperatorWithGroundings]
    We have a class for this, rather than just using a list, because we may be able to compress/amortize
    some data/compute this way.
    """

    @abstractmethod
    def get_affected_pvars(self) -> PVGSBound:
        raise NotImplementedError()

    @abstractmethod
    def get_non_guaranteed_pvars(
        self, initial_state_guaranteed: PartialStateType
    ) -> PVGSBound:
        """Maybe hard."""
        # TODO: Possibly the input should be something else with more structure, that lets us be more efficient.
        raise NotImplementedError()

    @abstractmethod
    def get_merged_operators(
        self: OWGS, initial_state: PartialStateType, relevant_pvars: PVGSBound
    ) -> OWGS:
        """This is probably the hardest thing to implement.
        Make sure to keep track of groundings for operator params, and groundings
        for quantifiers separately.

        Also: how do we cope with the initial_state when without grounding everything?
        """
        raise NotImplementedError("Child class should implement this")


OperatorCollectionType = TypeVar(
    "OperatorCollectionType", bound=OperatorWithGroundingsSet
)


PDDLTaskTypeVarUnbound = TypeVar("PDDLTaskTypeVarUnbound", bound="PDDLTask")


class PDDLTask(Generic[PVGSBound, GoalType, PartialStateType, OperatorCollectionType], ABC):
    """Holds a PDDL Task. Main thing passed into scoping probably. Needs to implement parsing."""

    all_operators: OperatorCollectionType
    all_pvars: PVGSBound
    initial_state: PartialStateType
    goal: GoalType
    pvars_grounding_type: Type[PVarGroundedSet[GoalType, PartialStateType]]

    @classmethod
    def from_domain_and_problem_files(
        cls: Type[PDDLTaskTypeVarUnbound], domain_path: str, problem_path: str
    ) -> PDDLTaskTypeVarUnbound:
        raise NotImplementedError("Child classes should implement this")

    def scope(self) -> tuple[OperatorCollectionType, PVGSBound]:
        """Get a compressed operator set sufficient for optimal planning.
        
        TODO: Should probably return a PDDLTask."""
        # Initialize relevant vars. TODO: What is the format?
        # I don't think it's just (lifted pvars, groundingsset) - we may need a union of these

        relevant_pvars_old = self.pvars_grounding_type.new_empty()
        relevant_pvars = (
            self.pvars_grounding_type.from_concrete_variable_value_assignment(self.goal)
        )
        merged_operators = self.all_operators  # Set this to convince pylance it is not unbound
        while relevant_pvars_old != relevant_pvars:
            # Get merged operators
            merged_operators = self.all_operators.get_merged_operators(
                self.initial_state, relevant_pvars
            )

            # Get affected variables
            # TODO: How do I get pylance to understand that affected_pvars_per_operator
            # has type all_operators.PVGS?
            # It's probably impossible in python - I think we need higher kinded types.
            # https://github.com/python/typing/discussions/999
            # https://github.com/python/typing/issues/548
            affected_pvars_per_operator: PVGSBound = merged_operators.get_affected_pvars()
            assert isinstance(affected_pvars_per_operator, self.pvars_grounding_type)
            # Get partial initial state over non-affected pvars
            initial_state_guaranteed = (
                affected_pvars_per_operator.mask_from_partial_state(self.initial_state)
            )

            # Update relevant pvars based on non-guaranteed preconditions
            relevant_pvars_old = relevant_pvars
            relevant_pvars = self.pvars_grounding_type.union(
                [
                    relevant_pvars,
                    merged_operators.get_non_guaranteed_pvars(initial_state_guaranteed),
                ]
            )

        # return merged_operators  # type: ignore This is never unbound.
        return (merged_operators, relevant_pvars)  # type: ignore
