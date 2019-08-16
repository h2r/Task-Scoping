import abc
import z3
"""
TODO
Get implies and violates (z3) working
Get rddl parser (pyrddl) working
Tweak scope() to be more general. In particular, have it deal with partially satisfied universal 
"""


class skill(abc.ABC):
	def get_precondition(self):
		pass
	def get_action(self):
		pass
	def get_effects(self):
		pass

class condition(abc.ABC):
	"""
	A condition is a first order expression that defines a set of states in a domain
	"""
	def get_variables(self):
		pass
	def evaluate(self, state):
		pass
	def get_related_vars(self):
		pass

def get_affecting_skills(condition, skills):
	#TODO: rewrite to work with condition and the actual data structures
	pass

def implies(a,b):
	"""Returns True if a implies b, else false"""
	#Use z3 to return prove(Not(And(b,Not(a))))
	pass

def violates(skill, condition):
	"""Returns True if executing the skill can lead to a violation of condition"""
	pass


def scope(goal, start_condition, skills):
	"""
	:param goal: first order logical expression classifying goal states.  
	:param skills: collection of (precondition, action, effect) triples
	"""
	#Conditions we have discovered in our causal search
	discovered = [goal]
	#The attributes that have an acceptable value in the start state, and are provably never changed to an unacceptable value
	#Note that rddl distinguished between changeable and constant variables, which allows this algorithm to work for, ex. passenger.loc == passenger.goal, since goal is constant
	guarantees = []
	used_skills = []
	#Conditions we have yet to deal with in our causal search
	q = [goal]  #queue
	#Do regression, assuming no action will interfere with gaurantees. Once the queue is empty,check whether actions broke gaurantees. Repeat until we are stable.
	while len(q) > 0:
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

		#Check whether the gaurantees hold
		violated_guarantees = []
		for g in guarantees:
			for s in used_skills:
				if violates(s,g):
					violated_guarantees.append(g)
					break  #Break out of inner loop, since we know the gaurantee is violated by some skill
		for g in violated_guarantees:
			q.append(g)
			guarantees.remove(g)

	discovered_not_guarantees = [c for c in discovered if c not in guarantees]
	return discovered_not_guarantees, used_skills


def scope_refactored(goal, start_condition, skills):
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

