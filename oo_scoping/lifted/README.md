# Lifted Scoping

This package introduces _Lifted Scoping_: Scoping without grounding all actions and variables. Hopefully this will allow scoping to be faster, and operate on problems too large to be grounded.

## Architecture

[abstract_groundings.py](abstract_groundings.py) holds

1. `PDDLTask`. The `PDDLTask.scope` method implements the scoping algorithm in a way generic to underlying data structures. 
2. Abstract base classes (ABCs) for the data structures. These define abstract methods that must be implemented in order for `PDDLTask.scope` to run. If you implement concrete subclasses for each of these ABCs, then you can use them with `PDDLTask.scope`.
   1. `PVarGroundedSet` holds a set of grounded pvars.
   2. `OperatorWithGroundingsSet` holds a set of grounded operators/actions.



## Implementations

### Classic

[enumerated_operators_like_og_scoping.py](enumerated_operators_like_og_scoping.py) implements the original, non-lifted scoping data structures. It uses lists of grounded pvars, and lists of grounded operators. For precondition handling, it uses z3.


### Cartesian

[cartesian.py](cartesian.py) uses a cartesian product factorization for groundings: For action $A$ with parameters $?x$ and $?y$ and, we express the groundings as $\{A(x, y) \mid (x, y) \in X \times Y \}$ for some sets of objects $X$ and $Y$.

#### Obstacles

1. Finding/implementing tool to handle lifted preconditions using first order logic. This will be an obstacle for all lifted scoping algorithms, except for trivial lifted-pvar-based scoping which ignores all groundings and requires no logic and just does backwards reachability from the lifted goal pvar. 
2. (Possible) Grounding sets not being cartesian products.
   1. (Current solution): Use upper-bound cartesian product representation. Preserves soundness, makes scoping less thorough. We'll probably use this for now.
   2. Use union-of-product representation, or some other lossless (or less lossy) representation. Possibly complicated and slow. 
   3. (PAC integration): Use estimates for variable/action significance to keep close to the product representation, discarding low significance groundings.
3. Is grounding the initial state a problem?


## Tests

[tests](../tests/) tests that our scoping algorithms work on some example domains. Currently, these example domains are minimal examples used to test trivial scoping, action merging, and causal links. Test definitions will be written in a scoper-agnostic manner, able to be used with any of our implementations, as long as the implementation has a method to convert it's outputs into a common format. For less-thorough scoping implementations, we'll need no weaken the test conditions.
