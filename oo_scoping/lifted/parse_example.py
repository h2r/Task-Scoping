import itertools
from dataclasses import dataclass
from typing import TypeVar

from pddl.logic import Constant, Variable
from pddl.action import Action
from pddl.parser.domain import Domain, DomainParser
from pddl.parser.problem import Problem, ProblemParser

from oo_scoping.test.domains.pickup_unlock_open import PickupUnlockOpenPaths
from oo_scoping.examples.paths import Minecraft3Paths

# dom = "oo_scoping/examples/domains/minecraft3/domain_minimally_unparseable_subtraction.pddl"
# with open(dom, "r") as f:
#     DomainParser()(f.read())

prob = "oo_scoping/examples/domains/minecraft3/problem_minimal_goal_equality_unparseable.pddl"
with open(prob, "r") as f:
    ProblemParser()(f.read())
