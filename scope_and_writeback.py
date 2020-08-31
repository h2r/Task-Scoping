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

if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "examples/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "examples/infinite-taxi-numeric/prob02.pddl"

    start_time = time.time()
    domain, problem = "examples/IPC_Domains/depot/DepotsNum.pddl", "examples/IPC_Domains/depot/prob-01.pddl"

def scope_pddl(domain, problem):
    parser = PDDL_Parser_z3()
    parser.parse_domain(domain)
    parser.parse_problem(problem)

    skill_list = parser.get_skills()

    # This below block converts all the domain's goals to z3
    goal_cond = parser.get_goal_cond()

    # This below block converts all the domain's initial conditions to z3
    init_cond_list = parser.get_init_cond_list()
   
    

    # Run the scoper on the constructed goal, skills and initial condition
    rel_pvars, rel_skills = scope(goals=goal_cond, skills=skill_list, start_condition=init_cond_list)
      
    # print("~~~~~Relevant skills~~~~~")
    # print("\n\n".join(map(str,rel_skills)))
    # print("~~~~~Relevant pvars~~~~~")
    # for p in rel_pvars:
    #     print(p)
 
    # print(rel_pvars)
    # print(rel_skills)

    
    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)
    all_pvars = get_unique_z3_vars(all_pvars)
    irrel_pvars = [p for p in map(str,all_pvars) if p not in map(str,rel_pvars)]
    all_objects = pvars2objects(all_pvars)
    rel_objects = pvars2objects(rel_pvars)
    irrel_objects = [x for x in all_objects if x not in rel_objects]

    # print(f"Irrelevant objects:")
    # print("\n".join(irrel_objects))
    scoped_problem_path = get_scoped_problem_path(problem)
    writeback_problem(problem, scoped_problem_path, irrel_objects)

    all_actions = sorted(list(set([a.name for a in parser.actions])))
    relevant_actions = []
    for s in rel_skills:
        if isinstance(s.action,str):
            relevant_actions.append(s.action)
        else:
            relevant_actions.extend(s.action)
    relevant_actions = sorted(list(set(relevant_actions)))
    irrel_actions = [a for a in all_actions if a not in relevant_actions]
    # print("~~~~~~~Irrel actions~~~~~~~")
    # for a in irrel_actions: print(a)
    scoped_domain_path = get_scoped_domain_path(domain, problem)
    writeback_domain(domain, scoped_domain_path, irrel_actions)

if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "examples/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "examples/infinite-taxi-numeric/prob02.pddl"

    start_time = time.time()
    domain, problem = "./examples/multi_monkeys_playroom/multi_monkeys_playroom.pddl", "./examples/multi_monkeys_playroom/prob-01.pddl"
    scope_pddl(domain, problem)
    

    end_time = time.time()
    print(f"Total time: {end_time - start_time}")