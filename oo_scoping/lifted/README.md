# Scoping V2

This is an attempt at lifted scoping. For now it's just the skeleton code and types. Bits we expect to be hard are marked.

## Overview
`scoping.py` has the scoping algorithm, written in terms of abstract classes which hold collections of operators/pvars.

`abstract_groundings.py` defines some abstract base classes for specifying collections of grounded pvars and operators, potentially compactly. These classes have abstract methods/classmethods for carrying out a portion of scoping. These abstract methods need to be overridden by implementation in concrete child classes.

The idea is that we will find smarter ways to implement the abstract classes, but `scoping.py` will remain unchanged.

## Planned implementations for collections of operators/pvars

Step 1: Implement them as we do in our current scoping repo - lists of fully grounded operators and pvars. `enumerated_operators_like_og_scoping.py` starts this (WIP).


Step 2: Factor out the groundings for each lifted operator/pvar, like `(lifted_operator, groundings)`. The groundings will (I think) always be the product set of the groundings for each parameter, so we can get a much more compact representation by just storing the per-parameter groundings.
`enumerated_operator_level_groundings.py` starts this.

Step 3: Make another improvement! One option is finding a more compact way to store the groundings from step 2. Maybe by adding the option to store the groundings as "all objects of type T", rather than listing out all the objects of type T, or "all objects of type T except for ...". I'm not sure if this will be the right next step. We should probably find/make domains where that strain version 2 and then go from there.


## Expected difficulties

Finding tool for manipulating lifted predicates. z3 doesn't handle first order logic - we patched over this by replacing `forall`/`exists` with conjunction/disjunction over the grounded propositions.

(Possible) Identifying when two predicates are equivalent up to renaming of parameters. I don't think we really need this for a v1.
