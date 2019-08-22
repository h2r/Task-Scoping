import abc
import z3
from classes import *
from utils import *
"""
TODO
Get rddl parser (pyrddl) working
Tweak scope() to be more general. In particular, have it deal with partially satisfied universal 
Have conditions, skills return collection of variables using forall quantifiers, ex. forall(p | not inTaxi(p))
Change how we check for guarantee violation. When we add a new skill, we should remove from the solver any conditions that depend on variables the skill affects
!!!Split preconditions by and
"""
def solver_implies_condition(solver, precondition):
	solver.push()
	# assert z3.is_expr(precondition), "{}; {}".format(type(precondition),precondition)
	# print(type(precondition))
	solver.add(z3.Not(precondition))
	result = solver.check()
	solver.pop()
	if result == z3.z3.unsat:
		# print("result: {}".format(result))
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown guarantee for precondition: {}".format(precondition))
		# print("result: {}".format(result))
		return False

def triplet_dict_to_triples(skill_dict):
	skill_triples = []
	for action in skill_dict.keys():
		for precondition, effect in skill_dict[action].items():
			skill_triples.append((precondition,action,effect))
	return skill_triples

def get_affecting_skills(condition, skills):
	#TODO: rewrite to work with Precondition and the actual data structures
	affecting_skills = []
	for s in skills:
		overlapping_vars = [v for v in get_var_names(condition) if v in s.get_affected_variables()]
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
	pass



