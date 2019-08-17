import abc
import z3
"""
TODO
Get implies and violates (z3) working
Get rddl parser (pyrddl) working
Tweak scope() to be more general. In particular, have it deal with partially satisfied universal 
Have conditions, skills return collection of variables using forall quantifiers, ex. forall(p | not inTaxi(p))
"""


class skill(abc.ABC):
	def get_precondition(self):
		pass
	def get_action(self):
		pass
	def get_affected_vars(self):
		"""
		:return: list of affected vars. May modify to use forall
		"""
		pass

class condition(abc.ABC):
	"""
	A condition is a first order expression that defines a set of states in a domain
	"""
	def get_variables(self):
		pass
	def evaluate(self, state):
		#z3 state implies condition
		pass


def get_overlapping_variables(vars0, vars1):
	"""
	:vars0: list of variables (TODO generalize to a quantified set)
	:vars1: list of variables (TODO generalize to a quantified set)
	:return: variables in both collections (TODO generalize to a quantified set)
	"""
	return [v for v in vars0 if v in vars1]

def get_affecting_skills(condition, skills):
	#TODO: rewrite to work with condition and the actual data structures
	pass

def implies(a,b):
	"""Returns True if a implies b, else false"""
	#Use z3 to return prove(Not(And(b,Not(a))))
	pass

def violates(skill, condition):
	"""Returns True if executing the skill can lead to a violation of condition"""
	common_vars = [v for v in skill.get_affected_vars() if v in condition.get_variables()]
	pass


def scope(goal, start_condition, skills):
	discovered = [goal]
	guarantees = []
	used_skills = []
	q = [goal]
	while len(q) > 0:
		bfs_with_guarantees(discovered,q,start_condition,skills, used_skills,guarantees)
		check_guarantees(guarantees,used_skills, discovered, q)
	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	return discovered_not_guarantees, used_skills

def bfs_with_guarantees(discovered,q,start_condition,skills, used_skills,guarantees):
	while len(q) > 0:
		condition = q.pop()
		#We are not trying to find a target (Is the start the target??), so we ignore this step
		#If not is_goal(v)
		for skill in get_affecting_skills(condition, skills):
			if skill in used_skills: continue
			used_skills.append(skill)
			precondition = skill.get_precondition()
			if precondition not in discovered:  #Could we do something fancier, like if discovered implies precondition?
				discovered.append(precondition)
				if implies(start_condition,precondition):
					guarantees.append(precondition)
				else:
					q.append(precondition)


def check_guarantees(guarantees,used_skills, discovered, q):
	violated_guarantees = []
	for g in guarantees:
		for s in used_skills:
			if violates(s,g):
				violated_guarantees.append(g)
				break  #Break out of inner loop, since we know the gaurantee is violated by some skill
	for g in violated_guarantees:
		q.append(g)
		guarantees.remove(g)
	return guarantees,

