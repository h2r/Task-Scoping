## 2023-12-07
We may want goal, partial state, to use implementation-specific representations. In which case we should make some functions/classes generic wrt the relevant types.

## 2023-12-09:
Started adding tests.

Tests for trivial irrelevance and causal irrelevance pass.

Next up: Test operator merging.

## 2023-12-10
Added minimal operator merging test. Both OG and refactored scoping pass.

## 2023-12-22
Refactored `merge` into partition skills and merge skills. This is to isolate the logic-using code as much as possible.
Started cartesian scoping.

## 2023-12-23
Progress on cartesian scoping. Next up is writing up how actions should be stored. I'll probably be vague wrt preconditions, since the actual implementation will need to use a logic tool. 
Groundings will be kept at the action level, while precondition, parameters, and effects will keep track of variable names and types, but no groundings.
