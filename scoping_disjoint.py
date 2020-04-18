from typing import List, Dict, Tuple, Union
from collections import OrderedDict
import abc, time
import z3
from classes import *
from utils import check_implication, solver_implies_condition, get_var_names, get_var_names_multi, \
	AndList, ConditionList,	and2, provably_contradicting, not2, and2, or2, \
	simplify_before_ors, condition_str2objects
from pyrddl_inspector import prepare_rddl_for_scoper
import pdb
from typing import Collection
"""
TODO later
Change how we check for guarantee violation. When we add a new skill, we should remove from the solver any conditions that depend on variables the skill affects
~"""

def get_quotient_skills(skills: Collection[Skill], denominator: Collection[str], solver: z3.Solver = None, use_jank_merge = False) \
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
		if use_jank_merge: new_cond = jank_merge(conds, solver)
		else: new_cond = clean_merge(conds, solver)
		new_skill = Skill(new_cond, action, effects)
		# Since we are using disjoint preconditions, we don't need to process the implicit effects
		new_skill.implicit_effects_processed = True
		new_skills.append(new_skill)
	return new_skills

def clean_merge(conds, solver, tactic='ctx-solver-simplify'):
	# TODO take care of conditionlists earlier
	disj = or2(*conds)
	if isinstance(disj, ConditionList): disj = disj.to_z3()
	g = z3.Goal()
	g.add(disj)
	disj_simp =  z3.Tactic(tactic)(g).as_expr()
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


def get_skills_targeting_pvar(var: str, skills: List[Skill]):
	return [s for s in skills if var in s.get_targeted_variables()]


def get_skills_affecting_pvar(var: str, skills: List[Skill]):
	return [s for s in skills if var in s.get_affected_variables()]


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
	common_vars = [v for v in skill.get_affected_variables() if v in get_var_names(condition)]
	return len(common_vars) > 0


def scope(goal, skills, start_condition=None, solver=None):
	if solver is None:
		solver = z3.Solver()
		solver.add(start_condition)
	converged = False
	all_pvars = get_all_effected_vars(skills)
	
	# Get irrelevant pvars so we can do initial quotienting
	relevant_pvars = []
	if not hasattr(goal,"__iter__"):
		goal = [goal]
	for x in goal:
		if not solver_implies_condition(solver, x):
			relevant_pvars += get_var_names(x)
	irrelevant_pvars = [x for x in all_pvars if x not in relevant_pvars]
	
	quotient_skills = get_quotient_skills(skills, denominator=irrelevant_pvars)

	while not converged:	
		relevant_pvars_old = relevant_pvars
		relevant_pvars, relevant_objects, used_skills = _scope(goal, quotient_skills, start_condition, solver)
		irrelevant_pvars = [x for x in all_pvars if x not in relevant_pvars]
		# pdb.set_trace()
		if relevant_pvars_old == relevant_pvars:
			converged = True
		else:
			quotient_skills = get_quotient_skills(skills, denominator=irrelevant_pvars)
			# pdb.set_trace()
	return relevant_pvars, relevant_objects, used_skills


def _scope(goal, skills, start_condition=None, solver=None):
	"""Runs the Task Scoping algorithm on a given goal, provided skills, a start_condition and a solver (z3)"""
	# Create solver from start_condition
	if solver is None:
		solver = z3.Solver()
		solver.add(start_condition)
	guarantees = []
	discovered = []
	q = []
	if hasattr(goal, "__iter__"):
		discovered = []
		for x in goal:
			discovered.append(x)
			if solver_implies_condition(solver, x):
				guarantees.append(x)
			else:
				q.append(x)

	# if type(goal) is AndList:
	# 	discovered = copy.copy(goal.args)
	# 	q = copy.copy(goal.args)
	else:  # TODO make symmetric with above. Currently won't scope everything when goal is true at start
		discovered = [goal]
		q = [goal]

	used_skills = []
	while len(q) > 0:
		bfs_with_guarantees(discovered, q, solver, skills, used_skills, guarantees)
		for s in used_skills:
			if (s.get_action() == "move_north()"): print(s)
		# pdb.set_trace()
		# print(f"bf len(used_skills): {len(used_skills)}")
		check_guarantees(guarantees, used_skills, q)
	# used_skills = list(set(used_skills))
	# pdb.set_trace()
	# print(f"cg len(used_skills): {len(used_skills)}")

	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	relevant_pvars = list(set([x for c in discovered_not_guarantees for x in get_var_names(c)]))
	relevant_objects = condition_str2objects(relevant_pvars)
	return relevant_pvars, relevant_objects, used_skills


def bfs_with_guarantees(discovered, q, solver, skills, used_skills, guarantees):
	"""
	This procedure essentially runs a Breadth-First Search that does the following:
	1. Finds all possible skills affecting every condition mentioned in the list q (all possible DOF's)
	2. Ensures that every precondition involved with these skills is dealt with
	So, at the end of this procedure, we should have chcked through all degrees of freedom,
	but unfortunately, some of the skills we're using could violate the guarantees we've made.
	We need to check if this is the case, then unguarantee these conditions and add them to q
	and rerun this search procedure.

	discovered: A list of conditions we already know about. We keep track of this to accumulate
	all the various preconditions we might need.
	q: A list of conditions to be met. Once we've accumulated skills such that all conditions in
	q are affected (i.e, all 'degrees of freedom' or 'effect types' are found for every condition
	in q), this procedure terminates.
	solver: A z3 solver that was instantiated and populated with domain variavles earlier
	skills: All CAE triples that've been parsed from the domain's transition dynamics directly
	used_skills: The list of CAE triples that need to be used
	guarantees: Conditions that we believe are guaranteed to not be violated throughout any of
	our trajectories.
	"""
	while len(q) > 0:
		# pdb.set_trace()
		condition = q.pop()

		# if("p1" in str(condition)):
		# 	pdb.set_trace()

		if type(condition) is AndList:
			print("dang")

		# We are not trying to find a target (Is the start the target??), so we ignore this step
		# If not is_goal(v)

		affecting_skills = get_skills_targeting_condition(condition, skills)

		for skill in affecting_skills:
			# if(skill.action == "toggle_blinker()"):
			# 	pdb.set_trace()

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
					# of things we care about? TODO: Not sure why the solver implying the precondition
					# makes it a guarantee. I'm somewhat unclear what this function even does.
					if solver_implies_condition(solver, precondition):
						guarantees.append(precondition)
					else:
						# if("p1" in str(precondition)):
						# 	pdb.set_trace()
						q.append(precondition)

			# if(skill.action == "move_north()"):
			# 	pdb.set_trace()


def check_guarantees(guarantees, used_skills, q):
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
		q.append(g)
		guarantees.remove(g)
	return guarantees


def scope_rddl_file(input_file_path, output_file_path, irrelevant_objects):
	"""
	:param input_file_path:
	:param output_file_path:
	:param irrelevant_objects: (type, name) list
	:return:
	"""
	with open(input_file_path, 'r') as f:
		input_lines = f.readlines()
	output_lines = []
	for l in input_lines:
		# Check whether line contains irrelevant object
		contains_irrelevant = False
		for (t, o) in irrelevant_objects:
			if o in l:
				contains_irrelevant = True
				# If this is an object declaration
				if l.strip()[:len(t)] == t:
					comma_split = l.split(",")
					comma_split_no_spaces = [x.replace(" ", "") for x in comma_split]
					o_id = comma_split_no_spaces.index(o)
					comma_split_o_removed = [comma_split[i] for i in range(len(comma_split)) if i != o_id]
					new_l = ",".join(comma_split_o_removed)
					output_lines.append(new_l)
				break
		if not contains_irrelevant:
			output_lines.append(l)
	with open(output_file_path, 'w') as f:
		f.writelines(output_lines)

if __name__ == "__main__":
	pass
