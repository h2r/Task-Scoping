from utils import get_atoms, get_unique_z3_vars, get_scoped_domain_path, get_scoped_problem_path, writeback_problem, writeback_domain, pvars2objects
from scoping import scope
from PDDLz3 import PDDL_Parser_z3
def scope_pddl(domain, problem, remove_cl_pvars = True):
    parser = PDDL_Parser_z3()
    parser.parse_domain(domain)
    parser.parse_problem(problem)

    skill_list = parser.get_skills()

    # This below block converts all the domain's goals to z3
    goal_cond = parser.get_goal_cond()

    # This below block converts all the domain's initial conditions to z3
    init_cond_list = parser.get_init_cond_list()
   
    

    # Run the scoper on the constructed goal, skills and initial condition
    rel_pvars, cl_pvars, rel_skills = scope(goals=goal_cond, skills=skill_list, start_condition=init_cond_list)
    
    

    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)
    all_pvars = get_unique_z3_vars(all_pvars)
    if remove_cl_pvars:
        irrel_pvars = [p for p in map(str,all_pvars) if p not in map(str,rel_pvars)]
    else:
        irrel_pvars = [p for p in map(str,all_pvars) if p not in map(str,rel_pvars + cl_pvars)]
    all_objects = pvars2objects(all_pvars)
    rel_objects = pvars2objects(rel_pvars)
    irrel_objects = [x for x in all_objects if x not in rel_objects]

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

    scoped_domain_path = get_scoped_domain_path(domain, problem)
    writeback_domain(domain, scoped_domain_path, irrel_actions)
