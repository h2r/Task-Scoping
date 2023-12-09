print("Starting scope and writeback imports")
import argparse
import copy
import itertools
import pprint
import re
import sys
import time
from collections import OrderedDict
from typing import Dict, Iterable, List, Tuple

import z3

from oo_scoping.action import Action
from oo_scoping.PDDLz3 import PDDL_Parser_z3
from oo_scoping.scoping import scope
from oo_scoping.skill_classes import EffectTypePDDL, SkillPDDL
from oo_scoping.utils import (
    condition_str2objects,
    get_atoms,
    get_unique_z3_vars,
    nested_list_replace,
    product_dict,
    pvars2objects,
)
from oo_scoping.writeback_pddl import (
    get_scoped_domain_path,
    get_scoped_problem_path,
    writeback_domain,
    writeback_problem,
)
from oo_scoping.z3_type_aliases import Z3Variable

print("Starting scope and writeback")



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
    rel_pvars, cl_pvars, rel_skills = scope(
        goals=goal_cond, skills=skill_list, start_condition=init_cond_list, verbose=0
    )

    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)

    def get_unique_pvars_in_scope_pddl(all_pvars):
        """
        Wrapper used to view this call in a profiler
        """
        return get_unique_z3_vars(all_pvars)

    all_pvars = map(str, all_pvars)
    all_pvars = sorted(list(set(all_pvars)))
    irrel_pvars = [p for p in map(str, all_pvars) if p not in map(str, rel_pvars)]
    all_objects = pvars2objects(all_pvars)
    rel_objects = pvars2objects(rel_pvars)
    irrel_objects = [x for x in all_objects if x not in rel_objects]

    scoped_problem_path = get_scoped_problem_path(problem)
    writeback_problem(problem, scoped_problem_path, irrel_objects)

    all_actions = sorted(list(set([a.name for a in parser.actions])))
    relevant_actions = []
    for s in rel_skills:
        if isinstance(s.action, str):
            relevant_actions.append(s.action)
        else:
            relevant_actions.extend(s.action)
    relevant_actions = sorted(list(set(relevant_actions)))
    irrel_actions = [a for a in all_actions if a not in relevant_actions]
    scoped_domain_path = get_scoped_domain_path(domain, problem)
    writeback_domain(domain, scoped_domain_path, irrel_actions)


if __name__ == "__main__":
    # Parse command line arguments to script
    argparser = argparse.ArgumentParser()
    argparser.add_argument("--domain", help="path to domain pddl file")
    argparser.add_argument("--prob", help="path to task pddl file")
    args = argparser.parse_args()
    # Run scoping and writeback!
    scope_pddl(args.domain, args.prob)
