from itertools import chain
from typing import Iterable, Union
import z3
from skill_classes import merge_skills, Skill, EffectType, SkillPDDL, EffectTypePDDL, merge_skills_pddl
from utils import split_conj, get_atoms, solver_implies_condition, simplify_disjunction, get_unique_z3_vars, writeback_domain, writeback_problem, pvars2objects


def get_causal_links(start_condition, skills):
	all_effects = sorted(list(set(chain(*[s.all_effects for s in skills]))))
	all_effected_pvars = sorted(list(set([x.pvar for x in all_effects])), key=lambda x: str(x))
	causal_links = []
	for c in start_condition:
		threatened_pvars = [x for x in get_atoms(c) if x in all_effected_pvars]
		if len(threatened_pvars) == 0: causal_links.append(c)
	return causal_links

def get_unlinked_pvars(skills, causal_links, dummy_goal, solver):
	solver.push()
	solver.add(*causal_links)
	pvars_rel_new = [dummy_goal]
	for s in skills:
		for prec in split_conj(s.precondition):
			if not solver_implies_condition(solver, prec):
				pvars_rel_new.extend(get_atoms(prec))
			# if(s.action == "turn_on_greenbutton"):
			# 	from IPython import embed; embed()

		# from IPython import embed; embed()

		# params are pvars that influence the effects of the skill. Ex. if a skill has effect (person.y += person.leg_length),
		# then leg_length is a parameter. params are different from preconditions in that a param can not be implied
		# by the start condition, so we always consider them unlinked. 
		if isinstance(s, SkillPDDL):
			pvars_rel_new.extend(s.params)
	pvars_rel_new = sorted(list(set(pvars_rel_new)), key=lambda x: str(x))
	solver.pop()
	return pvars_rel_new

def scope(goals: Union[Iterable[z3.ExprRef], z3.ExprRef], skills: Iterable[Skill]
		  , start_condition: Union[Iterable[z3.ExprRef], z3.ExprRef], state_constraints: z3.ExprRef = None
		  , verbose=0):
	if isinstance(goals, z3.ExprRef):
		# print("Splitting goals")
		goals = split_conj(goals)
		# print("Split goals")
	if isinstance(start_condition, z3.ExprRef):
		# print("Splitting initial condition")
		start_condition = split_conj(start_condition)
		# print("Split initial conditions")
	solver = z3.Solver()
	if state_constraints is not None:
		state_constraints_simple = simplify_disjunction(state_constraints)
		solver.add(state_constraints_simple)
	solver.push()
	if verbose > 0:
		print("~" * 10 + "Initial Conditions" + "~" * 10)
		print("\n\n".join(map(str,start_condition)))
		print('\n')
		print("~" * 10 + "Goals" + "~" * 10)
		print("\n\n".join(map(str,goals)))
		print("\n")
		print("~" * 10 + "State Constraints" + "~" * 10)
		print(state_constraints)

	# print("Starting to scope!")
	# We make a dummy goal and dummy final skill a la LCP because it simplifies the beginning of the algorithm.
	# We will remove the dummy goal and skill before returning the final results
	dummy_goal = z3.Bool("dummy_goal") #TODO make sure this var does not already exist
	dummy_goal_et = EffectTypePDDL(dummy_goal,0)
	dummy_final_skill = SkillPDDL(z3.And(*goals), "DummyFinalSkill",dummy_goal_et)
	skills = skills + [dummy_final_skill]
	pvars_rel = [dummy_goal]

	converged = False
	i = 0
	while not converged:
		# Get quotient skills
		skills_rel = merge_skills_pddl(skills, pvars_rel, solver=solver)
		if verbose > 1:
			print(i)
			print("~" * 10 + "Skills" + "~" * 10)
			print("\n\n".join(map(str,skills_rel)))
			print("\n")
			print("~" * 10 + "Pvars Rel" + "~" * 10)
			print("\n\n".join(map(str,pvars_rel)))
		# Get causal links
		causal_links = get_causal_links(start_condition, skills_rel)

		# Get pvars not guaranteed by causal links
		pvars_rel_new = get_unlinked_pvars(skills_rel, causal_links, dummy_goal, solver)

		# Check convergence
		converged = (pvars_rel == pvars_rel_new)

		pvars_rel = pvars_rel_new
		i += 1
		# print(pvars_rel)
		# from IPython import embed; embed()
		# from IPython.core.debugger import set_trace; set_trace()

	# Remove the dummy pvar and skill
	pvars_rel.remove(dummy_goal)
	skills_rel = [x for x in skills_rel if dummy_goal_et not in x.effects]
	# TODO set pvars_cl to only include pvars that matter in preconditions of rel_skills
	skills_conds_pvars = []
	for s in skills_rel:
		skills_conds_pvars.extend(get_atoms(s.precondition))
	skills_conds_pvars = get_unique_z3_vars(skills_conds_pvars)

	pvars_cl = []
	for c in causal_links:
		pvars_cl.extend(get_atoms(c))
	pvars_cl = get_unique_z3_vars(pvars_cl)
	pvars_cl = [c for c in pvars_cl if c not in skills_conds_pvars]
	return pvars_rel, pvars_cl, skills_rel

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
    rel_pvars, cl_pvars, rel_skills = scope(goals=goal_cond, skills=skill_list, start_condition=init_cond_list)
    
    all_pvars = []
    for s in skill_list:
        all_pvars.extend(get_atoms(s.precondition))
        all_pvars.extend(s.params)
    all_pvars = get_unique_z3_vars(all_pvars)
    irrel_pvars = [p for p in map(str,all_pvars) if p not in map(str,rel_pvars)]
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
