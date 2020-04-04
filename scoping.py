from typing import List, Dict, Tuple, Union
from collections import OrderedDict
import abc, time
import z3
from utils import condition_str2objects
from classes import *
from logic_utils import check_implication, solver_implies_condition, get_var_names, AndList, OrList, ConditionList, and2
from pyrddl_inspector import prepare_rddl_for_scoper
# import pdb

"""
TODO
Change how we check for guarantee violation. When we add a new skill, we should remove from the solver any conditions that depend on variables the skill affects
~"""


def get_implied_effects(skills: List[Skill], fast_version= False) -> List[Skill]:
	"""
	Update each skill with the variables implicity affected by it. Ex. Moving with a passenger in the taxi explicitly moves the passenger, implicitly moves the taxi
	Note: This would be faster if we had a partial ordering of skills. We could then start at the root skills (no implied effects), see their effects on their children, etc,
	using get_all_affected_variables() instead of get_targeted_variables()
	Alternatively/additionally, we could put this into cython (would it help? itertools.product should be fast already)
	:param skills:
	:return:
	"""
	solver = z3.Solver()
	implication_time = 0
	if not fast_version:
		for (s0,s1) in itertools.product(skills,skills):
			if s0.get_action() == s1.get_action():
				implication_start = time.time()
				if check_implication(s0.get_precondition(), s1.get_precondition()):
					s0.implicitly_affected_variables.extend(s1.get_targeted_variables())
				implication_time += time.time() - implication_start
		for s in skills:
			s.implicitly_affected_variables = list(set(s.implicitly_affected_variables))
			s.implicit_effects_processed = True
	if fast_version:
		pass
	print("Get_implied_effects implication time: {}".format(implication_time))
	return skills

def move_var_from_implied_to_target(skills: List[Skill], vars: List[str]) -> List[Skill]:
	"""
	For any skill which affects, but does not target, a var in vars, split the skill into a version that targets var
	and a version that does not affect var.
	"""
	"""
	Pseudocode: For each skill s that accidentally affects var, find the skills with stronger preconditions that target x.
		Conjoin s.prec with AND(NOT(si.prec))
	Speed up by storing poset structure? This is probably going to be real slow
	"""
# 	Naive, probably painfully slow version
	for var in vars:
		targeting_skills, accidentally_affecting_skills = get_targeting_and_accidentally_affecting_skills(var, skills)
		# Accidental skill: A skill that may have unintended side-effects (eg. (no wall, move_north, taxi y ++))
		# may also affect p0.y for example (if p0 is in the taxi already)
		# Targeting skills are skills that will always have a certain effect on a variable
		
		for accidental_skill in accidentally_affecting_skills:
			negated_refined_preconditions = []
			for targeting_skill in targeting_skills:
				if targeting_skill.get_action() == accidental_skill.get_action() and \
						check_implication(targeting_skill.get_precondition(), accidental_skill.get_precondition()):
					# Add effect to targeting skill
					targeting_skill.effect.extend(accidental_skill.get_targeted_variables())
					# Update the accidental_skill's precondition to exclude the targeting skill
					cond = targeting_skill.get_precondition()
					if isinstance(cond, ConditionList): #TODO turn negated orlist into andlist of negations
						cond = cond.to_z3()
					negated_refined_preconditions.append(z3.Not(cond))
			accidental_skill.precondition = and2(accidental_skill.precondition, *negated_refined_preconditions)
			# accidental_skill.effect.append(var)
			accidental_skill.implicitly_affected_variables.remove(var)

def move_var_from_implied_to_target_test():
	# TODO actually test
	rddl_file_location = "./taxi-rddl-domain/taxi-structured-deparameterized_actions.rddl"
	goal_conditions, necessarily_relevant_pvars, skill_triplets, solver = prepare_rddl_for_scoper(rddl_file_location)
	clean_AndLists(skill_triplets)
	get_implied_effects(skill_triplets)
	print("~~~~~Skills~~~~~")
	for s in skill_triplets:
		if s.get_action() == "move_north()": print(s)
	move_var_from_implied_to_target(skill_triplets, ['passenger-y-curr(p0)'])
	print("~~~~~Skills~~~~~")
	for s in skill_triplets:
		if s.get_action() == "move_north()": print(s)
	# relevant_vars, used_skills = scope(goal_conditions,skill_triplets,solver=solver)
	# print("\n~~~Relevant objects~~~")
	# for x in relevant_vars: print(x)
	# print("\n~~~Relevant skills~~~")
	# for s in used_skills: print(s)
	# used_actions = sorted(list(set([s.get_action() for s in used_skills])))
	# print("\n~~~Relevant Actions~~~")
	# for a in used_actions: print(a)

def triplet_dict_to_triples(skill_dict: Dict[str,Dict[str,List[Union[z3.z3.ExprRef,AndList]]]]) -> Tuple[Union[z3.z3.ExprRef,AndList],str,List[str]]:
	"""
	:param skill_dict: [action][effect] -> List[preconditions]
	"""
	skill_triples = []
	for action in skill_dict.keys():
		for effect, precondition in skill_dict[action].items():
			skill_triples.append(Skill(precondition, action, [effect]))
	return skill_triples

def get_affecting_skills(condition, skills):
	affecting_skills = []
	for s in skills:
		condition_vars = get_var_names(condition)
		skill_targets = s.get_targeted_variables()
		overlapping_vars = [v for v in condition_vars if v in skill_targets]
		if len(overlapping_vars) > 0:
			affecting_skills.append(s)
	return affecting_skills

def get_targeting_and_accidentally_affecting_skills(var: str, skills: List[Skill]):
	targeting_skills = [s for s in skills if var in s.get_targeted_variables()]
	affecting_skills = [s for s in skills if var in s.get_affected_variables()]
	accidentally_affecting_skills = [s for s in affecting_skills if s not in targeting_skills]
	return targeting_skills, accidentally_affecting_skills
# def implies(a,b):
# 	"""Returns True if a implies b, else false"""
# 	#Use z3 to return prove(Not(And(b,Not(a))))
# 	pass

def violates(skill, condition):
	"""Returns True if executing the skill can lead to a violation of Precondition"""
	common_vars = [v for v in skill.get_affected_variables() if v in get_var_names(condition)]
	return len(common_vars) > 0


def scope(goal, skills, start_condition = None, solver=None):
	"""Runs the Task Scoping algorithm on a given goal, provided skills, a start_condition and a solver (z3)"""
	# TODO figure out when to run move_var_from_implied_to_target(). After it runs, update the precondions in q as appropriate.
	if solver is None:
		solver = z3.Solver()
		solver.add(start_condition)
	guarantees = []
	discovered = []
	q = []
	if hasattr(goal,"__iter__"):
		discovered = []
		for x in goal:
			discovered.append(x)
			if solver_implies_condition(solver,x):
				guarantees.append(x)
			else:
				q.append(x)

	# if type(goal) is AndList:
	# 	discovered = copy.copy(goal.args)
	# 	q = copy.copy(goal.args)
	else: #TODO make symmetric with above. Currently won't scope everything when goal is true at start
		discovered = [goal]
		q = [goal]

	used_skills = []
	#Create solver from start_condition

	while len(q) > 0:
		bfs_with_guarantees(discovered,q,solver,skills,used_skills,guarantees)
		# pdb.set_trace()
		# print(f"bf len(used_skills): {len(used_skills)}")
		check_guarantees(guarantees,used_skills,q)
		# pdb.set_trace()
		# print(f"cg len(used_skills): {len(used_skills)}")

	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	relevant_conditions = list(set([x for c in discovered_not_guarantees for x in get_var_names(c)]))
	relevant_objects = condition_str2objects(relevant_conditions)
	return relevant_objects, used_skills

def bfs_with_guarantees(discovered,q,solver,skills,used_skills,guarantees):
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
		if type(condition) is AndList:
			print("dang")
		#We are not trying to find a target (Is the start the target??), so we ignore this step
		#If not is_goal(v)
		
		affecting_skills = get_affecting_skills(condition, skills)
		
		for skill in affecting_skills:
			# if(skill.action == "toggle_blinker()"):
			# 	pdb.set_trace()

			if skill in used_skills: continue # We've already accumulated the degree of freedom for this condition
			used_skills.append(skill) # Else. add the skill to the list
			precondition = skill.get_precondition()
			if type(precondition) is AndList:
				precondition_list = copy.copy(precondition.args)
			else:
				precondition_list = [precondition]
			# Now, we've accumulated a list of preconditions that need to be met for the above 
			# skill to ever execute
			for precondition in precondition_list:
				if precondition not in discovered:  #Could we do something fancier, like if discovered implies precondition?
					discovered.append(precondition)					
					if type(precondition) is AndList: # The conditions should already be broken so this can't happen
						pass
					# Either the solver implies the precondition, or we need to append it to the list
					# of things we care about? TODO: Not sure why the solver implying the precondition
					# makes it a guarantee. I'm somewhat unclear what this function even does.
					if solver_implies_condition(solver,precondition):
						guarantees.append(precondition)
					else:
						q.append(precondition)
					
					# if(skill.action == "move_north()"):
					# 	pdb.set_trace()


def check_guarantees(guarantees,used_skills,q):
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
			if violates(s,g):
				violated_guarantees.append(g)
				break  #Break out of inner loop, since we know the gaurantee is violated by some skill
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
		#Check whether line contains irrelevant object
		contains_irrelevant = False
		for (t,o) in irrelevant_objects:
			if o in l:
				contains_irrelevant = True
				#If this is an object declaration
				if l.strip()[:len(t)] == t:
					comma_split = l.split(",")
					comma_split_no_spaces = [x.replace(" ","") for x in comma_split]
					o_id = comma_split_no_spaces.index(o)
					comma_split_o_removed = [comma_split[i] for i in range(len(comma_split)) if i != o_id]
					new_l = ",".join(comma_split_o_removed)
					output_lines.append(new_l)
				break
		if not contains_irrelevant:
			output_lines.append(l)
	with open(output_file_path,'w') as f:
		f.writelines(output_lines)

def test_get_implied_effects():
	raise NotImplementedError()
	pass

def scope_rddl_file_test():
	input_file_path = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"

def clean_AndLists(skills):
	"""
	Removes "True" from AndLists
	"""
	for s in skills:
		precond = s.get_precondition()
		if isinstance(precond,AndList):
			new_AndList = and2(*[x for x in precond if x is not True])
			s.precondition = new_AndList

def run_scope_on_file(rddl_file_location):
	algorithm_sections = ["pyrddl_inspector","clean_AndLists", "get_implied_effects", "scope"]
	boundary_times = []
	boundary_times.append(time.time())
	goal_conditions, necessarily_relevant_pvars, skill_triplets, solver = prepare_rddl_for_scoper(rddl_file_location)
	boundary_times.append(time.time())
	clean_AndLists(skill_triplets)
	boundary_times.append(time.time())
	get_implied_effects(skill_triplets)
	boundary_times.append(time.time())

	print("\n~~~~Starting Scope()~~~~\n")
	relevant_vars, used_skills = scope(goal_conditions,skill_triplets,solver=solver)
	relevant_vars = relevant_vars + [str(i) for i in necessarily_relevant_pvars]
	relevant_vars = list(set(relevant_vars))
	boundary_times.append(time.time())

	print("times:")
	for section_id, section_name in enumerate(algorithm_sections):
		section_time = boundary_times[section_id+1] - boundary_times[section_id]
		print("{}: {}".format(section_name,section_time))
	print("\n~~~Relevant objects~~~")
	for r in relevant_vars:
		print(r)
	print("\n~~~Relevant skills~~~:")
	for s in used_skills:
		print(s)

	used_actions = sorted(list(set([s.get_action() for s in used_skills])))
	print("\n~~~Relevant Actions~~~")
	for a in used_actions: print(a)
	return relevant_vars, used_skills, used_actions

def domain_tests():
	"""
	Checks that scoping works correctly on some sample domains
	TODO check used_skills
	"""
	paths = OrderedDict()
	paths["taxi"] = "./taxi-rddl-domain/taxi-structured-deparameterized_actions.rddl"
	paths["taxi_p1_in_taxi"] = "./taxi-rddl-domain/taxi-structured-deparameterized_actions-p1-in-taxi.rddl"
	correct_objects = OrderedDict()
	correct_objects["taxi"] = {"t0", "p0", "w0"}
	correct_objects["taxi_p1_in_taxi"] = {"t0", "p0", "p1", "w0"}
	correct_actions = OrderedDict()
	correct_actions["taxi"] = {"move_north()", "move_west()", "move_south()", "move_east()", "pickup(p0)", "dropoff(p0)"}
	correct_actions["taxi_p1_in_taxi"] = {"move_north()", "move_west()", "move_south()", "move_east()", "pickup(p0)", "dropoff(p0)", "dropoff(p1)", "pickup(p1)"}
	successes, failures = [], []
	action_successes = []
	state_successes = []
	for domain, path in paths.items():
		relevant_vars, used_skills, used_actions = run_scope_on_file(path)
		if set(relevant_vars) == correct_objects[domain]: state_successes.append(domain)
		if set(used_actions) == correct_actions[domain]: action_successes.append(domain)
		else: failures.append(domain)

	print("\n\n~~~~~~~~~~~~~~~~~~~\n")
	print("Domain | Object Success | Action success")
	for d in paths.keys():
		print(f"{d} | {d in state_successes} | {d in action_successes}")
	# print("Successes:")
	# for d in successes: print(d)
	# print("Failures:")
	# for d in failures: print(d)

if __name__ == "__main__":
	file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions.rddl"
	# file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions-p1-in-taxi.rddl"
	# file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions_blinker.rddl"
	# file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions_complex.rddl"
	# file_path = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
	# file_path = "button-domains/button_special_button.rddl"
	# file_path = "button-domains/button_sum_reward.rddl"
	# file_path = "button-domains/button.rddl"
	# file_path = "button-domains/button_elif.rddl"
	# file_path = "misc-domains/academic-advising_composite_01.rddl"
	# file_path = "button-domains/button_door_negative_precondition.rddl"
	# file_path = "./enum-domains/enum-taxi-deparameterized-move-actions-nishanth.rddl"

	run_scope_on_file(file_path)
	#
	# domain_tests()
	# move_var_from_implied_to_target_test()
