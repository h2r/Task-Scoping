"""Simple non-collection-of-groundings classes."""
from __future__ import annotations

from dataclasses import dataclass
from typing import List, Optional, TypeVar, Type
from abc import ABC, abstractmethod, abstractclassmethod


@dataclass
class PartialState:
    """Value assignments to some, but not all, variables.

    We may end up needing a 'lifted' version, that lets us express this more compactly for large domains.
    Or maybe a dict version.
    """

    assignments: List[ConcreteVariableValueAssignment]



@dataclass
class ConcreteVariableValueAssignment:
    """Used for goal. We likely want so use something else."""

    pass


@dataclass
class PVarWithGroundings:
    """We maybe never need this instead of PVarGroundedSet.
    Wait, what's this even for? A _single_ grounding? Or many? I think many. Maybe delete this.
    """

    pass

    @classmethod
    def from_concrete_variable_value_assignment(
        cls, cvva: ConcreteVariableValueAssignment
    ) -> PVarWithGroundings:
        raise NotImplementedError()



@dataclass
class PreconditionLifted:
    """Precondition, with free parameters that need to be filled. Filling the free parameters gives a grounded effect."""

    pass


@dataclass
class EffectLifted:
    """Effect, with free parameters that need to be filled. Filling the free parameters gives a grounded effect."""

    pass

@dataclass
class GroundingsSet:
    """A set of groundings. Each grounding is a mapping from free parameter to concrete object."""

    pass


@dataclass
class ObjectType:
    """Type of an object. Eg ball, brick. Will be used in EffectLifted, etc."""

    name: str

@dataclass
class OperatorLifted:
    """Can represent merged or atomic operator"""

    precondition: PreconditionLifted
    effect: EffectLifted
    atomic_operators: Optional[List[OperatorLifted]]
    """None iff this operator is atomic. List of atomic operators otherwise. Or maybe list of component operators."""

