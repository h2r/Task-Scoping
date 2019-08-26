from typing import List, Dict, Tuple, Union
import abc, time
import z3
# from utils import *
from classes import *
from logic_utils import check_implication, solver_implies_condition, get_var_names, AndList, OrList
from pyrddl_inspector import prepare_rddl_for_scoper
"""
TODO
Change how we check for guarantee violation. When we add a new skill, we should remove from the solver any conditions that depend on variables the skill affects
~"""


def get_implied_effects(skills: List[Skill]) -> List[Skill]:
	"""
	Update each skill with the variables implicity affected by it. Ex. Moving with a passenger in the taxi explicitly moves the passenger, implicitly moves the taxi
	Note: This would be faster if we had a partial ordering of skills
	:param skills:
	:return:
	"""
	solver = z3.Solver()
	for (s0,s1) in itertools.product(skills,skills):
		if s0.get_action() == s1.get_action() and check_implication(s0.get_precondition(), s1.get_precondition()):
			s0.implicitly_affected_variables.extend(s1.get_targeted_variables())
	for s in skills:
		s.implicitly_affected_variables = list(set(s.implicitly_affected_variables))
		s.implicit_effects_processed = True
	return skills
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
	#TODO: rewrite to work with Precondition and the actual data structures
	affecting_skills = []
	for s in skills:
		overlapping_vars = [v for v in get_var_names(condition) if v in s.get_targeted_variables()]
		if len(overlapping_vars) > 0:
			affecting_skills.append(s)
	return affecting_skills

# def implies(a,b):
# 	"""Returns True if a implies b, else false"""
# 	#Use z3 to return prove(Not(And(b,Not(a))))
# 	pass

def violates(skill, condition):
	"""Returns True if executing the skill can lead to a violation of Precondition"""
	common_vars = [v for v in skill.get_affected_variables() if v in get_var_names(condition)]
	return len(common_vars) > 0


def scope(goal, skills, start_condition = None, solver=None):
	if solver is None:
		solver = z3.Solver()
		solver.add(start_condition)
	if type(goal) is AndList:
		discovered = copy.copy(goal.args)
		q = copy.copy(goal.args)
	else:
		discovered = [goal]
		q = [goal]

	guarantees = []
	used_skills = []
	#Create solver from start_condition

	while len(q) > 0:
		bfs_with_guarantees(discovered,q,solver,skills, used_skills,guarantees)
		check_guarantees(guarantees,used_skills, discovered, q)
	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	relevant_vars = list(set([x for c in discovered_not_guarantees for x in get_var_names(c)]))
	return relevant_vars, used_skills

def bfs_with_guarantees(discovered,q,solver,skills, used_skills,guarantees):
	while len(q) > 0:
		condition = q.pop()
		if type(condition) is AndList:
			print("dang")
		#We are not trying to find a target (Is the start the target??), so we ignore this step
		#If not is_goal(v)
		for skill in get_affecting_skills(condition, skills):
			if skill in used_skills: continue
			used_skills.append(skill)
			precondition = skill.get_precondition()
			if type(precondition) is AndList:
				precondition_list = copy.copy(precondition.args)
			else:
				precondition_list = [precondition]
			for precondition in precondition_list:
				if precondition not in discovered:  #Could we do something fancier, like if discovered implies precondition?
					if str(precondition) == "passenger-in-taxi_1_0":
						print("booooiii")
					discovered.append(precondition)
					if type(precondition) is AndList:
						print(skill)
					if solver_implies_condition(solver,precondition):
						guarantees.append(precondition)
					else:
						q.append(precondition)


def check_guarantees(guarantees,used_skills, discovered, q):
	violated_guarantees = []
	for g in guarantees:
		for s in used_skills:
			if violates(s,g):
				if 'passenger-in-taxi_1_0' in get_var_names(g):
					print("ruroh")
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
			new_AndList = AndList(*[x for x in precond if x is not True])
			s.precondition = new_AndList
def run_scope_on_file(rddl_file_location):
	algorithm_sections = ["pyrddl_inspector","clean_AndLists", "get_implied_effects", "scope"]
	boundary_times = []
	boundary_times.append(time.time())
	compiled_reward, skill_triplets, solver = prepare_rddl_for_scoper(rddl_file_location)
	# print("all skills:")
	# for s in skill_triplets: print(s)
	# print("Goal:\n".format(compiled_reward))
	boundary_times.append(time.time())
	clean_AndLists(skill_triplets)
	boundary_times.append(time.time())
	get_implied_effects(skill_triplets)
	boundary_times.append(time.time())
	relevant_vars, used_skills = scope(compiled_reward,skill_triplets,solver=solver)
	boundary_times.append(time.time())

	print("relevant_vars:")
	for r in relevant_vars:
		print(r)
	print("times:")
	for section_id, section_name in enumerate(algorithm_sections):
		section_time = boundary_times[section_id+1] - boundary_times[section_id]
		print("{}: {}".format(section_name,section_time))

if __name__ == "__main__":
	# file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions.rddl"
	file_path = "./taxi-rddl-domain/taxi-structured-deparameterized_actions_complex.rddl"
	# file_path = "button-domains/button_special_button.rddl"
	run_scope_on_file(file_path)
