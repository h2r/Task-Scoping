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
from utils import product_dict, nested_list_replace, get_atoms
from scoping import scope


if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    # taxi_dom = "examples/infinite-taxi-numeric/taxi-domain.pddl"
    # taxi_prob = "examples/infinite-taxi-numeric/prob02.pddl"

    taxi_dom, taxi_prob = "./examples/existential-taxi/taxi-domain.pddl", "./examples/existential-taxi/prob02.pddl"

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
      
    print("~~~~~Relevant skills~~~~~")
    print("\n\n".join(map(str,rel_skills)))
    print("~~~~~Relevant pvars~~~~~")
    for p in rel_pvars:
        print(p)
 
    # print(rel_pvars)
    # print(rel_skills)

