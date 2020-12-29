from itertools import chain
from typing import Iterable, Union
import z3
from oo_scoping.skill_classes import Skill, EffectType, SkillPDDL, EffectTypePDDL, merge_skills_pddl
from oo_scoping.utils import split_conj, get_atoms, solver_implies_condition, simplify_disjunction, get_unique_z3_vars, writeback_domain, writeback_problem, pvars2objects

def skills2effects(skills):
	"""
	Return union of effects from skills.
	Created as separate function for profiling purposes.
	"""
	return sorted(list(set(chain(*[s.all_effects for s in skills]))))


def effects2pvars(effects):
	"""
	Return union of pvars from effects.
	Created as separate function for profiling purposes.
	"""
	return sorted(list(set([x.pvar for x in effects])), key=lambda x: str(x))

def get_unthreatened_conditions(conditions, effected_pvars):
	"""
	Return list of conditions that are unthreatened by effected_pvars.
	Created as separate function for profiling purposes.
	"""
	# Map effected_pvars to str to make equality checking faster
	effected_pvars_s = [str(x) for x in effected_pvars]
	causal_links = []
	for c in conditions:
		atoms_z3 = get_atoms(c)
		atoms_s = [str(x) for x in atoms_z3]
		threatened_pvars = [x for x in atoms_s if x in effected_pvars_s]
		if len(threatened_pvars) == 0: causal_links.append(c)
	return causal_links

def get_unthreatened_conditions_slow(conditions, effected_pvars):
	"""
	Return list of conditions that are unthreatened by effected_pvars.
	Created as separate function for profiling purposes.
	This version keeps z(steve)
	"""
	causal_links = []
	for c in conditions:
		threatened_pvars = [x for x in get_atoms(c) if x in effected_pvars]
		if len(threatened_pvars) == 0: causal_links.append(c)
	return causal_links

def get_causal_links(start_condition, skills):
	"""
	:param start_condition: Condition we assume is true at start of trajectory
	:param skills: Iterable of Skills
	Returns list of conditions used by skills that are satisfied by start_condition and unthreatened by any skill
	"""
	all_effects = skills2effects(skills)
	all_effected_pvars = effects2pvars(all_effects)
	# causal_links = get_unthreatened_conditions(start_condition, all_effected_pvars)
	causal_links = get_unthreatened_conditions_slow(start_condition, all_effected_pvars)
	# causal_links = []
	# for c in start_condition:
	# 	threatened_pvars = [x for x in get_atoms(c) if x in all_effected_pvars]
	# 	if len(threatened_pvars) == 0: causal_links.append(c)
	return causal_links

def get_causal_links_old(start_condition, skills):
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
	# Debug
	stevewashere = False
	print("Done grounding! Starting to scope!!!")
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
		# causal_links = get_causal_links_old(start_condition, skills)

		print("Got new causal links!!!")
		# Get pvars not guaranteed by causal links
		pvars_rel_new = get_unlinked_pvars(skills_rel, causal_links, dummy_goal, solver)
		# Debug
		if "z(steve)" in map(str, pvars_rel_new):
			stevewashere = True
		else:
			if stevewashere:
				print("Steve vanished!")
				print("\n".join(map(str,pvars_rel_new)))
		# Check convergence
		converged = (pvars_rel == pvars_rel_new)

		pvars_rel = pvars_rel_new
		i += 1
		if verbose > 0:
			print("~~~Pvars Rel~~~")
			print(pvars_rel)

		print(f"Finished iteration {i}.")
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
	# TODO either return str vars, or speed up get_unique_z3_vars
	skills_conds_pvars = get_unique_z3_vars(skills_conds_pvars)

	pvars_cl = []
	for c in causal_links:
		pvars_cl.extend(get_atoms(c))
	pvars_cl = get_unique_z3_vars(pvars_cl)
	# We only care about the pvars that are causally linked AND used in preconditions
	pvars_cl = [c for c in pvars_cl if c in skills_conds_pvars]
	print("~~~Pvars Causally Linked~~~")
	print(pvars_cl)
	return pvars_rel, pvars_cl, skills_rel