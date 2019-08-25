import copy
from abc import ABC
import z3
import itertools
from instance_building_utils import *
def acceptable_z3_condition(x):
	Z3_HANDLED_TYPES = [z3.z3.ExprRef, bool]
	for t in Z3_HANDLED_TYPES:
		if isinstance(x,t):
			return True
	return False

def get_all_groundings(base_str, names, keys):
	name_lists = [names[k] for k in keys]
	object_name_sequence_list = itertools.product(*name_lists)
	x = object_name_sequence_list
	# x = list([i[0] for i in object_name_sequence_list])
	groundings = [g2n_names(base_str,object_names) for object_names in x]
	return groundings

class Skill():
	def __init__(self, precondition, action, effect):
		"""
		:param precondition: Precondition object
		:param action: string
		:param effect: list of affected variables
		"""
		self.precondition = precondition
		self.action = action
		self.effect = effect
		self.implicitly_affected_variables = []
		self.implicit_effects_processed = False
	def get_precondition(self):
		return self.precondition
	def get_action(self):
		return self.action
	def get_targeted_variables(self):
		return self.effect
	def get_affected_variables(self):
		if not self.implicit_effects_processed:
			raise ValueError("Implicit effects of this skill not yet processed")
		return self.effect + self.implicitly_affected_variables
	def __repr__(self):
		return "({},{},{})".format(self.get_precondition(),self.get_action(),self.get_targeted_variables())
	def __str__(self):
		return self.__repr__()

class Precondition():
	"""
	A Precondition is a first order expression that defines a set of states in a domain
	"""
	def __init__(self, variables, z3_condition):
		self.variables = variables
		self.z3_condition = z3_condition
	def get_variables(self):
		return self.variables
	def get_z3(self, state):
		return self.z3_condition

class UngroundedThing():
	def __init__(self, name, arguments):
		self.name = name
		self.arguments = arguments
	def ground(self, object_names):
		#If there are no args, it is already grounded
		if len(self.arguments) == 0:
			return [self.name]
		else:
			return get_all_groundings(self.name,  object_names, self.arguments)

class DomainAttribute(UngroundedThing):
	def __init__(self, name, type, arguments, constraints = ()):
		super().__init__(name,arguments)
		# self.name = name
		self.type = type
		self.constraints = constraints
		# self.arguments = arguments
		self.object_counts = {}
		self.groundings = []

class DomainAction(UngroundedThing):
	def __init__(self, name, arguments):
		super().__init__(name,arguments)
		# self.name = name
		# self.arguments = arguments

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
		self.z3_combinator = z3.And


class OrList(ConditionList):
	def __init__(self, *args):
		super().__init__(*args)
		self.name = "OrList"
		self.z3_combinator = z3.Or

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
if __name__ == "__main__":
	test_AndList()
	test_ConditionList()