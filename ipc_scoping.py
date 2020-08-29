from action import Action
# from PDDL import PDDL_Parser
from PDDLz3 import PDDL_Parser_z3
import sys, pprint
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
import re, copy, json
import itertools
import z3
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms, get_all_objects, condition_str2objects
from scoping import scope
import time

def pvars2objects(pvars):
    objs = condition_str2objects(map(str,pvars))
    objs = [s.strip() for s in objs]
    objs = sorted(list(set(objs)))
    return objs

def scope_file(domain, problem):
    parser = PDDL_Parser_z3()
    parser.parse_domain(domain)
    print("Parsed domain")
    parser.parse_problem(problem)
    print("Parsed problem")
    with open(problem, "r") as f:
        if ":metric" in f.read():
            raise ValueError(":metric makes the parser or scoper freeze")
    skill_list = parser.get_skills()
    print("Got skills")
    # This below block converts all the domain's goals to z3
    goal_cond = parser.get_goal_cond()
    print("Got goal")
    # This below block converts all the domain's initial conditions to z3
    init_cond_list = parser.get_init_cond_list()
    print("Got initial state")
    # Run the scoper on the constructed goal, skills and initial condition
    rel_pvars, rel_skills = scope(goals=goal_cond, skills=skill_list, start_condition=init_cond_list,verbose=0)

    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)
    all_objects = pvars2objects(all_pvars)
    rel_objects = pvars2objects(rel_pvars)
    irrel_objects = [x for x in all_objects if x not in rel_objects]
    irrel_pvars = [str(x) for x in all_pvars if str(x) not in map(str, all_pvars)]

    # return rel_objects, irrel_objects
    return rel_pvars, irrel_pvars
dom = "examples/Rovers/Strips/StripsRover.pddl"
for i in range(3,10): #nada up to 4
    prob = f"examples/Rovers/Strips/pfile{i}"
    print(f"({dom}, {prob})")
    start_time = time.time()
    try:
        rel, irrel = scope_file(dom, prob)
        r = irrel
    except Exception as e:
        r = e
    duration = time.time() - start_time
    r = (duration, r)
    print(f"Parse and scope time: {duration}")
    print(f"Irrelevant pvars: {r}")
