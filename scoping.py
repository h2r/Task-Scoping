from itertools import chain
from typing import Iterable, Union
import z3
from skill_classes import merge_skills, Skill, EffectType, SkillPDDL, EffectTypePDDL, merge_skills_pddl
from utils import split_conj, get_atoms, solver_implies_condition, simplify_disjunction


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
	return pvars_rel, skills_rel