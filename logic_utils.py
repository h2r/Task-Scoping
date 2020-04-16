from abc import ABC
import copy
import z3
import pdb
from typing import Union, List

solver = z3.Solver()
synth2varnames = {}



def get_var_names(expr):
	global synth2varnames

	if isinstance(expr, bool):
		return []
	vars = []
	for i in z3.z3util.get_vars(expr):
		i = str(i)
		if i in synth2varnames.keys():
			vars = vars + synth2varnames[i]
		else:
			vars.append(i)
	return sorted(list(set(vars)))

def get_var_names_multi(expressions):
	"""Gets var names for a list of expressions"""
	pvars = []
	for e in expressions:
		pvars.extend(get_var_names(e))
	pvars = sorted(list(set(pvars)))

def solver_implies_condition(solver, precondition):
	# print("Assertions:")
	# for a in solver.assertions(): print(a)
	solver.push()
	# assert z3.is_expr(precondition), "{}; {}".format(type(precondition),precondition)
	# print(type(precondition))
	solver.add(z3.Not(precondition))
	# print("Assertions (including not precondition):")
	# for a in solver.assertions(): print(a)
	# print("Assertions over")
	result = solver.check()
	solver.pop()
	if result == z3.z3.unsat:
		# print("result: {}".format(result))
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown guarantee for precondition: {}".format(precondition))
			raise TimeoutError("solver returned unknown")
		# print("result: {}".format(result))
		return False

def check_implication(antecedent, consequent):
	if isinstance(antecedent,AndList):
		antecedent = antecedent.to_z3()
	if isinstance(consequent,AndList):
		consequent = consequent.to_z3()
	global solver
	# We need to push and pop!
	solver.push()
	solver.add(antecedent)
	solver.add(z3.Not(consequent))
	result = solver.check()
	solver.pop()
	if result == z3.z3.unsat:
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown implication for precondition: {} => {}".format(antecedent,consequent))
		return False

def provably_contradicting(*args, my_solver = None):
	# Returns True if we can prove a and b are contradictory. False otherwise.
	# Pass in a solver if you want to use background information to check the contradiction.
	# You should probably only pass in a solver that contains propositions about constants
	# We use the name my_solver instead of solver to avoid mucking with the global var.
	global solver
	if my_solver is None: my_solver = solver
	my_solver.push()
	for x in args:
		if isinstance(x,ConditionList):
			x = x.to_z3()
		my_solver.add(x)
	result = my_solver.check()
	my_solver.pop()
	# If it is sat, or unknown, return False
	return result == z3.z3.unsat

def get_implies(x,y):
	return ((not x) or y)

def get_iff(x,y):
	both_true = and2(x,y)
	both_false = and2(z3.Not(x),z3.Not(y))
	# pdb.set_trace()
	try:
		return or2(both_true,both_false)
	except Exception as e: print(f"{type(both_true)}, {type(both_false)}")

def simplify_before_ors(cond1, cond2):
	"""
	From boolean algebra, we know: a*b + a*b' = a*(b + b') = a*(1) = a
	This function applies that to a list of conditions to be or'ed
	cond1 and cond2 must both be AndLists that have no contradictions inherent in them!
	(i.e: no having both A and z3.Not(A) in the same list)
	"""
	if(isinstance(cond1, AndList) and isinstance(cond2, AndList)):
		if(len(cond1.args) != len(cond2.args)):
			return [cond1, cond2]
		else:
			positive_cond_list = set()
			negative_cond_list = set()
			for condA in cond1:
				if(condA.decl().name() == str(condA)):
					positive_cond_list.add(str(condA))
				elif(condA.decl().name() == 'not'):
					negative_cond_list.add(str(condA.arg(0)))
			for condB in cond2:
				if(condB.decl().name() == str(condB)):
					positive_cond_list.add(str(condB))
				elif(condB.decl().name() == 'not'):
					negative_cond_list.add(str(condB.arg(0)))

			to_purge = []
			for po_cond in positive_cond_list:
				if(po_cond in negative_cond_list):
					to_purge.append(po_cond)

			new_cond1 = []
			new_cond2 = []
			for condA in cond1:
				keep_elem = True
				for purgee in to_purge:
					if(purgee in str(condA)):
						keep_elem = False
				if(keep_elem):
					new_cond1.append(condA)

			for condB in cond2:
				keep_elem = True
				for purgee in to_purge:
					if(purgee in str(condB)):
						keep_elem = False
				if(keep_elem):
					new_cond2.append(condB)

			if(new_cond1 == new_cond2):
				return [AndList(*new_cond1)]
			else:
				return [AndList(*new_cond1), AndList(*new_cond2)]
			
	else:
		return [cond1, cond2]

def or2(*x, solver=None):
	"""
	A wrapper for z3.Or meant to handle ConditionLists and simplifications based on the constant conditions
	"""
	if len(x) == 0: return False
	elif len(x) == 1: return x[0]
	else:
		new_x = []
		for i in x:
			if isinstance(i,ConditionList):
				new_x.append(i.to_z3())
			else:
				new_x.append(i)
		try:
			condition = z3.Or(*new_x)
		except z3.z3types.Z3Exception as e:
			print("Busted in or2")
			for x in new_x: print(f"{x}: {type(x)}")
			raise e
		if solver is not None:
			if solver_implies_condition(solver, condition):
				condition = True
		return condition

		# Note, the below if_else statement exists solely to deal with Or's that only have 1
		# condition in them
		# if(len(new_x) > 1):
		# 	condition = z3.Or(*new_x)
		# else:
		# 	condition = new_x[0]
		#
		# if solver is not None:
		# 	if solver_implies_condition(solver, condition):
		# 		condition = True
		# return condition

def and2(*x):
	"""
	If there are multiple args, creates an AndList. Else, returns the original expression
	"""
	if len(x) == 0: return True
	elif len(x) == 1: return x[0]
	else:
		return AndList(*x)

def not2(x):
	if isinstance(x,ConditionList):
		x = x.to_z3()
	return z3.Not(x)

class ConditionList(ABC):
	def __init__(self, *args, name, z3_combinator):
		#If any of the args are an AndList, flatten them
		self.args = self.flatten(args)
		self.z3_combinator = z3_combinator
		self.name = name
	def flatten(self,a):
		new_list = []
		for x in a:
			if isinstance(x, type(self)):
				new_list.extend(self.flatten(x))
			elif isinstance(x,ConditionList):
				new_list.append(x)
			else:
				#If x a z3 expression, add it to the list
				z3_acceptable = acceptable_z3_condition(x)
				if z3_acceptable:
					new_list.append(x)
				else:
					print(type(x))
					raise TypeError("Don't know how to flatten {}".format(x))
		return new_list
	def to_z3(self):
		arg_list = []
		for c in self.args:
			if acceptable_z3_condition(c):
				arg_list.append(c)
			elif isinstance(c,ConditionList):
				arg_list.append(c.to_z3())
			else:
				raise TypeError("Do not know how to handle {}".format(c))
		return self.z3_combinator(*arg_list)
	def __getitem__(self, item):
		return self.args[item]
	def __iter__(self):
		return self.args.__iter__()
	def __repr__(self):
		return "{}({})".format(self.name,self.args)
	def __str__(self):
		return self.__repr__()

class AndList(ConditionList):
	def __init__(self, *args):
		super().__init__(*args, name="AndList", z3_combinator=z3.And)

class OrList(ConditionList):
	def __init__(self, *args):
		super().__init__(*args, name="OrList", z3_combinator=or2)

def acceptable_z3_condition(x):
	Z3_HANDLED_TYPES = [z3.z3.ExprRef, bool]
	for t in Z3_HANDLED_TYPES:
		if isinstance(x,t):
			return True
	return False

def get_atoms(expr: Union[bool,z3.ExprRef, z3.Goal, ConditionList]) -> List[z3.ExprRef]:
	if isinstance(expr, bool): return []
	if isinstance(expr, ConditionList):
		expr = expr.to_z3()
	if isinstance(expr, z3.Goal):
		expr = expr.as_expr()
	atoms = []
	children = expr.children()
	# An expression is an atom iff it has no children
	if len(children) == 0:
		atoms = [expr]
	else:
		atoms = []
		for c in children:
			atoms.extend(get_atoms(c))
	return atoms

def get_atoms_test():
	A = z3.Bool('A')
	B = z3.Bool('B')
	both = z3.And(A,B)
	Aonly = z3.And(A,z3.Not(B))
	Acomp = z3.Or(both,Aonly)
	assert set(get_atoms(both)) == {A,B}, set(get_atoms(both))
	assert set(get_atoms(Aonly)) == {A,B}, set(get_atoms(Aonly))

def test_AndList():
	z3_vars = [z3.Bool(str(i)) for i in range(10)]
	a_correct = z3_vars[1:3]
	a = AndList(*z3_vars[1:3])
	b_correct = z3_vars[0:1] + a_correct
	c_correct = z3_vars[4:6]
	d_correct = b_correct + c_correct
	b = AndList(z3_vars[0],a)
	c = AndList(*z3_vars[4:6])
	d = AndList(b,c)
	assert d.args == d_correct, "{}\n{}".format(d.args,d_correct)

def test_ConditionList():
	z3_vars = [z3.Bool(str(i)) for i in range(10)]
	#Test an and of ors
	ors = [OrList(*z3_vars[i:i+2]) for i in range(0,len(z3_vars),2)]
	and0 = AndList(*ors)
	and0_z3 = and0.to_z3()
	print(and0)
	print(and0_z3)

def split_conjunction(x):
	"""Not implemented. Thought I could do something with sexpr, but that might just be equivalent to str(), and I'm not sure how to get references to the composite conditions from it.
	I thought we had some issue with not being able to see pieces of a composite expression, but I rememvber now the issue was decomposing the ast itself, not the string"""
	pass

def split_conjunction_test():
	x = z3.Bool('x')
	y = z3.Bool('y')
	x_and_y = z3.And(x,y)
	print(x_and_y)

if __name__ == "__main__":
	# p0 = z3.Bool('passenger-in-taxi(p0)')
	# p1 = z3.Bool('passenger-in-taxi(p1)')
	# c1 = AndList(*[z3.Not(p0),z3.Not(p1)])
	# c2 = AndList(*[z3.Not(p0),p1])
	# print(simplify_before_ors(c1, c2))
	get_atoms_test()
