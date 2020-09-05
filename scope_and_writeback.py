from action import Action
# from PDDL import PDDL_Parser
from PDDLz3 import PDDL_Parser_z3
import sys, pprint
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
import re, copy
import itertools
import z3
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms, get_all_objects\
    , condition_str2objects, writeback_problem, writeback_domain\
        , get_scoped_problem_path, get_scoped_domain_path, pvars2objects, get_unique_z3_vars
from scoping import scope
import time

from pddl_scoper import scope_pddl

if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "examples/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "examples/infinite-taxi-numeric/prob02.pddl"

    start_time = time.time()
    domain, problem = "examples/IPC_Domains/SatRovers/SatRovers.pddl", "examples/IPC_Domains/SatRovers/prob-01.pddl"
    scope_pddl(domain, problem, remove_cl_pvars=False, scoping_suffix="with_cl")
    
    end_time = time.time()
    print(f"Total time: {end_time - start_time}")