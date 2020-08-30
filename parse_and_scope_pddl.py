import re, copy, itertools, z3, time, sys, pprint
from action import Action
from PDDLz3 import PDDL_Parser_z3
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms, get_all_objects, condition_str2objects, writeback_problem, get_scoped_problem_path
from scoping import scope

if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "examples/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "examples/infinite-taxi-numeric/prob02.pddl"

    start_time = time.time()
    taxi_dom, taxi_prob = "./examples/multi_monkeys_playroom/multi_monkeys_playroom.pddl", "./examples/multi_monkeys_playroom/prob-09.pddl"

    domain, problem = taxi_dom, taxi_prob

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

    def pvars2objects(pvars):
        objs = condition_str2objects(map(str,pvars))
        objs = [s.strip() for s in objs]
        objs = sorted(list(set(objs)))
        return objs
    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)
    all_objects = pvars2objects(all_pvars)
    rel_objects = pvars2objects(rel_pvars)
    irrel_objects = [x for x in all_objects if x not in rel_objects]

    # print(f"Relevant objects:")
    # print("\n".join(rel_objects))
    writeback_problem(taxi_prob, "./examples/multi_monkeys_playroom/prob-09_scoped.pddl", irrel_objects)

    end_time = time.time()
    print(f"Total time: {end_time - start_time}")