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

## 2023-12-24

Q: Do we need to take into account groundings when partitioning by effects for cartesian scoping? If so, how?
    Suppose the grounding sets for actions differ for the vars in an effect.
    How would this be? ~~I _think_ in scoping, grounding sets are shared across actions, so~~
    ~~this shouldn't be an issue. In a future hierarchical scoping, actions may have different grounding sets.~~

~~Taking a step back, we probably don't need to store a bunch of separate sets of groundings. We probably can just store~~

1. Global groundings (list of all objects of each type)
2. Relevant groundings (currently relevant objects of each type)
3. ?Newly relevant groundings (based on newly relevant preconditions)

Wait, this is false. Scoping really cares about grounded pvars. It's possible for an object to be relevant for one pvar, but not another. 

I should think this through from the perspective of actions/objects being initially added as relevant.

The core: RelevantPvars is a _single_ cartesian grounded set of pvars. Each pvar within it may have different groundings. But any single pvar has _one_ set of groundings. Actions are relevant if they affect relevant pvars. If two actions each have only one effect, and it's on the same lifted pvar, then the groundings will be shared.

But if action1 has an extra effect on another pvar, which has different relevant groundings, then when comparing the shared lifted effect of action0 and action1, action1's effect will have "more groundings", but they won't matter. Need to be careful about breaking causal links.


## 2023-12-31
[This](https://github.com/AI-Planning/pddl) PDDL parser fixed issues which prevented it from parsing our minecreaft domain. I think we can use it now (if we replace subtraction with adding a negative number. They're working on that issue, too). It seems to have much better typing than our current, janky, copied-to-this-repo parser, so we should use it going forwards.

Working on getting relevant effects from cartesian actions.
