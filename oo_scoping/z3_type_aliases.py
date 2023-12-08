"""Type aliases for z3 objects. These let us express assumptions/interpretations of variables in type signatures."""

from typing import TypeAlias, List

import z3


Z3Variable: TypeAlias = z3.ExprRef
"""A z3 expression representing a single grounded pvar. eg `x-position(passenger0)`"""


Z3ValueAssignment: TypeAlias = z3.ExprRef
"""A z3 expression representing a value-assignment to a variable. Eg `x-position(passenger0) == 3`
TODO: Maybe this should be for z3.BoolRef?"""

Z3ValueAssignmentList: TypeAlias = List[Z3ValueAssignment]
"""List of Z3ValueAssignment. Can represent a partial state."""
