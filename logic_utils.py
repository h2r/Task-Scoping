from abc import ABC
import z3

def get_var_names(expr):
	if isinstance(expr, bool):
		return []
	vars = [str(i) for i in z3.z3util.get_vars(expr)]
	return vars
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
		# print("result: {}".format(result))
		return False

def check_implication(antecedent, consequent):
	#TODO make global empty solver instead of creating new one every time. Creating a solver may take nontrivial time
	if isinstance(antecedent,AndList):
		antecedent = antecedent.to_z3()
	if isinstance(consequent,AndList):
		consequent = consequent.to_z3()
	solver = z3.Solver()
	solver.add(antecedent)
	solver.add(z3.Not(consequent))
	result = solver.check()
	if result == z3.z3.unsat:
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown implication for precondition: {} => {}".format(antecedent,consequent))
		return False

def or2(*x, solver=None):
	"""
	A wrapper for z3.Or meant to handle ConditionLists and simplifications based on the constant conditions
	"""
	new_x = []
	for i in x:
		if isinstance(i,ConditionList):
			new_x.append(i.to_z3())
		else:
			new_x.append(i)
	condition = z3.Or(*new_x)
	if solver is not None:
		if solver_implies_condition(solver, condition):
			condition = True
	return condition

def and2(*x, solver=None):
	"""
	A wrapper for z3.And meant to handle ConditionLists and simplifications based on the constant conditions
	"""
	new_x = []
	for i in x:
		if isinstance(i,ConditionList):
			new_x.append(i.to_z3())
		else:
			new_x.append(i)
	condition = z3.And(*new_x)
	if solver is not None:
		if solver_implies_condition(solver, condition):
			condition = False
	return condition

class ConditionList(ABC):
	def __init__(self, *args):
		#If any of the args are an AndList, flatten them
		self.args = self.flatten(args)
		self.z3_combinator = None
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
		super().__init__(*args)
		self.name = "AndList"
		self.z3_combinator = and2


class OrList(ConditionList):
	def __init__(self, *args):
		super().__init__(*args)
		self.name = "OrList"
		self.z3_combinator = or2
def acceptable_z3_condition(x):
	Z3_HANDLED_TYPES = [z3.z3.ExprRef, bool]
	for t in Z3_HANDLED_TYPES:
		if isinstance(x,t):
			return True
	return False
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
