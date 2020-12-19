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
    # zeno_dom = "domains/zeno/zeno.pddl"
    # zeno_prob = "domains/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "domains/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "domains/infinite-taxi-numeric/prob02.pddl"

    start_time = time.time()
    domain, problem = "domains/IPC_Domains/CompositeIPC/ipc_composite.pddl", "domains/IPC_Domains/CompositeIPC/prob-01.pddl"
    # domain, problem = "domains/IPC_Domains/depot/DepotsNum.pddl", "domains/IPC_Domains/depot/pfile2"
    scope_pddl(domain, problem)
    
    end_time = time.time()
    print(f"Total time: {end_time - start_time}")