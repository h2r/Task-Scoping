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
    problem = "examples/minecraft2/prob_obsidian.pddl"
    scope_pddl(domain, problem)
    
    end_time = time.time()
    print(f"Total time: {end_time - start_time}")