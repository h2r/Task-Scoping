"""Core scoping algorithm. Defined using abstract groundings classes, so that we can plug in 
whichever concrete grounding implementation we want."""
from __future__ import annotations

from oo_scoping.lifted.abstract_groundings import *
from oo_scoping.lifted.atomic_classes import *


def scope(
    operators_lifted: OperatorWithGroundingsSet,
    initial_state: PartialState,
    goal: ConcreteVariableValueAssignment,
    pvar_groundings_type: Type[PVarGroundedSet],
) -> OperatorWithGroundingsSet:
    """Get a compressed operator set sufficient for optimal planning.

    Args:
        operators_lifted: Characterizes the set of lifted operators and all possible groundings.
            The groundings will ideally be specified in a compact way.
        initial_state: Partial initial state.
        goal: Assumed to be a single variable-value assignment, WLOG.

    TODO: Take in scopingtask instead. Probably.
    """
    # Initialize relevant vars. TODO: What is the format?
    # I don't think it's just (lifted pvars, groundingsset) - we may need a union of these

    relevant_pvars_old = pvar_groundings_type.new_empty()
    relevant_pvars = pvar_groundings_type.from_concrete_variable_value_assignment(goal)

    while relevant_pvars_old != relevant_pvars:
        # Get merged operators
        merged_operators = operators_lifted.get_merged_operators(
            initial_state, relevant_pvars
        )

        # Get affected variables
        affected_pvars_per_operator = merged_operators.get_affected_pvars()

        # Get partial initial state over non-affected pvars
        initial_state_guaranteed = affected_pvars_per_operator.mask_from_partial_state(
            initial_state
        )

        # Update relevant pvars based on non-guaranteed preconditions
        relevant_pvars_old = relevant_pvars
        relevant_pvars = pvar_groundings_type.union(
            [
                relevant_pvars,
                merged_operators.get_non_guaranteed_pvars(initial_state_guaranteed),
            ]
        )

    return merged_operators  # type: ignore This is never unbound.
