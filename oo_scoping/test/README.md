# Tests

TODO: Add tests that we can scope minimal domains with:

1. trivial irrelevance
2. operator-merging based irrelevance
3. causal link irrelevance

We'll define these domains, along with the correct scoping.

Test architecture:

1. Base test definition class that is scoper agnostic
2. Subclasses of the test definition class that use specific scopers

This lets us apply the same tests to multiple scopers, without needing to repeat the core test code.


## pickup-unlock-open domain
Pickup key to unlock door to open door. All binary variables, only 3 actions.

The most obvious way to write this domain involves a single object - door - and 3 pvars. But if we do that, then we can't scope objects, only pvars. Which actually is fine, if our writeback handles that. If it doesn't, we can mod it. In any case, the logic is simpler this way, so we'll roll with it and adjust the test code as needed.


## Questions

Should we store the correct answers in pddl? How could we? I don't want to just store correctly-scoped PDDL,
because PDDL can't express that a grounded pvar is relevant/irrelevant, it can only scope out entire objects and lifted pvars.

So we'd need to use comments. Eh, too jank. Let's just write the test conditions in python.
