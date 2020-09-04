from PDDLz3 import PDDL_Parser_z3
import sys, pprint
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
import re, copy
from scoping import scope
import time
from pddl_scoper import scope_pddl


if __name__ == '__main__':
    start_time = time.time()
    domain = "examples/minecraft2/minecraft-contrived2.pddl"
    # problems = ["examples/minecraft2/prob_obsidian_with_pick.pddl", "examples/minecraft2/prob_obsidian_without_pick.pddl"]
    problems = [
        "examples/minecraft2/prob_irrel_obsidian_with_pick.pddl"
        # "examples/minecraft2/prob_irrel_flint_with_pick.pddl"
        # "examples/minecraft2/prob_irrel_nether_with_pick.pddl"
    ]

    for problem in problems:
        scope_pddl(domain, problem, remove_cl_pvars=False, scoping_suffix="keep_cl")
        # scope_pddl(domain, problem, remove_cl_pvars=True, scoping_suffix="remove_cl")

    end_time = time.time()
    print(f"Total time: {end_time - start_time}")