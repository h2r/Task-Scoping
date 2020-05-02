from typing import List, Dict, Tuple, Union
from collections import OrderedDict
import abc, time
import z3
from classes import *
from utils import check_implication, solver_implies_condition, get_var_names, get_var_names_multi, \
	AndList, ConditionList, and2, provably_contradicting, not2, and2, or2, \
	simplify_before_ors, condition_str2objects
from pyrddl_inspector import prepare_rddl_for_scoper
import pdb
from typing import Collection


def get_quotient_skills(skills: Collection[Skill], denominator: Collection[str], solver: z3.Solver = None,
						use_jank_merge=False) \
		-> Collection[Skill]:
	"""
	:param skills: collection of concrete skills
	:param denominator: collection of pvars we are going to quotient out
	:param solver: solver to use when taking disjunction of preconditions. Used to simplify some disjunctions.
		Should only contain expressions that are always true, ie nonfluents.
	:return: collection of abstract skills. AKA the quotient list of skills: skills/denominator
	"""
	# Maps a pair of an action and sorted tuple of pvars to the list of preconditions that, under that action,
	# have those effects
	pvars2skills = {}
	for s in skills:
		effects = tuple(sorted([v for v in s.get_targeted_variables() if v not in denominator]))
		# pdb.set_trace()
		k = (s.get_action(), effects)
		if k not in pvars2skills.keys():
			pvars2skills[k] = []
		pvars2skills[k].append(s.get_precondition())
	new_skills: List[Skill] = []

	for (action, effects), conds in pvars2skills.items():
		if use_jank_merge:
			new_cond = jank_merge(conds, solver)
		else:
			new_cond = clean_merge(conds, solver)
		new_skill = Skill(new_cond, action, effects)
		# Since we are using disjoint preconditions, we don't need to process the implicit effects
		new_skill.implicit_effects_processed = True
		new_skills.append(new_skill)
	return new_skills


def clean_merge(conds, solver, tactic='aig'):
	# TODO take care of conditionlists earlier
	disj = or2(*conds)
	if isinstance(disj, ConditionList): disj = disj.to_z3()
	g = z3.Goal()
	g.add(disj)
	disj_simp = z3.Tactic(tactic)(g).as_expr()
	if disj_simp.decl().name() == 'and':
		disj_simp = and2(*disj_simp.children())
	return disj_simp


def jank_merge(conds, solver):
	if (len(conds) == 0):
		new_cond = or2(*conds, solver=solver)
	elif (len(conds) == 1):
		new_cond = conds[0]
	elif (len(conds) == 2):
		simp_conds = simplify_before_ors(conds[0], conds[1])
		if (len(simp_conds) == 1):
			new_cond = simp_conds[0]
		elif (len(simp_conds) == 2):
			new_cond = or2(*simp_conds, solver=solver)
	else:
		raise ValueError(
			'We are trying to merge skills where there are more than 2 combined preconds. Code for this not-yet implemented')
	return new_cond


def get_skills_targeting_condition(condition, skills):
	"""
	:return: skills that target any of condition's pvars
	"""
	affecting_skills = []
	condition_vars = get_var_names(condition)
	for s in skills:
		skill_targets = s.get_targeted_variables()
		overlapping_vars = [v for v in condition_vars if v in skill_targets]
		if len(overlapping_vars) > 0:
			affecting_skills.append(s)
	return affecting_skills


def get_skills_targeting_pvar(var: Union[str, List[str]], skills: List[Skill]):
	if isinstance(var, str):
		var = [var]
	tgt_skills = []
	for v in var:
		tgt_skills.extend([s for s in skills if var in s.get_targeted_variables()])
	return list(set(tgt_skills))


def get_skills_affecting_pvar(var: str, skills: List[Skill]):
	return [s for s in skills if var in s.get_explicit_affected_variables()]


def get_targeting_and_accidentally_affecting_skills(var: str, skills: List[Skill]):
	"""
	:return: skills that target, and skills that accidentally affect, the pvar
	"""
	targeting_skills = get_skills_targeting_pvar(var, skills)
	affecting_skills = get_skills_affecting_pvar(var, skills)
	accidentally_affecting_skills = [s for s in affecting_skills if s not in targeting_skills]
	return targeting_skills, accidentally_affecting_skills


def violates(skill, condition):
	"""Returns True if executing the skill can lead to a violation of Precondition"""
	common_vars = [v for v in skill.get_explicit_affected_variables() if v in get_var_names(condition)]
	return len(common_vars) > 0


def scope(goal, skills, start_condition=None, solver=None):
	# Create solver from start_condition
	if solver is None:
		solver = z3.Solver()
		solver.add(start_condition)

	# TODO We do this basically twice. Merge them.
	all_pvars = get_all_effected_vars(skills)
	# Get irrelevant pvars so we can do initial quotienting
	relevant_pvars = []
	if not hasattr(goal, "__iter__"):
		goal = [goal]
	for x in goal:
		if not solver_implies_condition(solver, x):
			relevant_pvars += get_var_names(x)
	irrelevant_pvars = [x for x in all_pvars if x not in relevant_pvars]

	quotient_skills = get_quotient_skills(skills, denominator=irrelevant_pvars)

	guarantees = []
	discovered = []
	if hasattr(goal, "__iter__"):
		discovered = []
		for x in goal:
			discovered.append(x)
			if solver_implies_condition(solver, x):
				guarantees.append(x)
	else:  # TODO merge with above
		discovered = [goal]
		q = [goal]

	converged = False
	while not converged:
		relevant_pvars_old = relevant_pvars
		relevant_pvars, relevant_objects, used_skills, discovered, guarantees = _scope(discovered, guarantees, skills,
																					   goal, quotient_skills,
																					   start_condition, solver)
		irrelevant_pvars = [x for x in all_pvars if x not in relevant_pvars]
		# pdb.set_trace()
		if relevant_pvars_old == relevant_pvars:
			converged = True
		else:
			quotient_skills = get_quotient_skills(skills, denominator=irrelevant_pvars)
		# pdb.set_trace()
	return relevant_pvars, relevant_objects, used_skills


def _scope(discovered, guarantees, orig_skills, goal, skills, start_condition=None, solver=None):
	used_skills = []
	one_step_bfs(discovered, solver, skills, used_skills, guarantees)

	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	relevant_pvars = list(set([x for c in discovered_not_guarantees for x in get_var_names(c)]))
	effecting_original_skills = get_skills_targeting_pvar(relevant_pvars, orig_skills)
	# check_guarantees(guarantees, effecting_original_skills)
	check_guarantees(guarantees, orig_skills)

	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	relevant_pvars = list(set([x for c in discovered_not_guarantees for x in get_var_names(c)]))
	relevant_objects = condition_str2objects(relevant_pvars)
	return relevant_pvars, relevant_objects, used_skills, discovered, guarantees


def one_step_bfs(discovered, solver, skills, used_skills, guarantees):
	affecting_skills = []

	for skill in skills:
		if (skill.effect):
			affecting_skills.append(skill)

	# pdb.set_trace()

	for skill in affecting_skills:

		if skill in used_skills: continue  # We've already accumulated the degree of freedom for this condition
		used_skills.append(skill)  # Else. add the skill to the list
		precondition = skill.get_precondition()

		if isinstance(precondition, AndList):
			raise TypeError(f"AndList: {precondition}")
			precondition_list = copy.copy(precondition.args)
		elif z3.is_expr(precondition) and precondition.decl().name() == 'and':
			precondition_list = precondition.children()
		else:
			precondition_list = [precondition]
		# Now, we've accumulated a list of preconditions that need to be met for the above
		# skill to ever execute
		for precondition in precondition_list:
			if precondition not in discovered:  # Could we do something fancier, like if discovered implies precondition?
				discovered.append(precondition)
				if type(precondition) is AndList:  # The conditions should already be broken so this can't happen
					raise TypeError(f"AndList: {precondition}")
				# Either the solver implies the precondition, or we need to append it to the list
				# of things we care about
				if solver_implies_condition(solver, precondition):
					guarantees.append(precondition)


def check_guarantees(guarantees, used_skills):
	"""
	This procedure essentially checks if our BFS from the above procedure has found any skills that
	may violate any of the guarantees we've made. If so, it removes the corresponding guarantee
	and adds it to q as a new precondition to be checker and guaranteed.
	:param q: A list of conditions to be met. Once we've accumulated skills such that all conditions in
	q are affected (i.e, all 'degrees of freedom' or 'effect types' are found for every condition
	in q), this procedure terminates.
	:param used_skills: The list of CAE triples that need to be used
	:param guarantees: Conditions that we believe are guaranteed to not be violated throughout any of
	our trajectories.
	"""
	violated_guarantees = []
	for g in guarantees:
		for s in used_skills:
			if violates(s, g):
				violated_guarantees.append(g)
				break  # Break out of inner loop, since we know the gaurantee is violated by some skill
	for g in violated_guarantees:
		guarantees.remove(g)
	return guarantees
