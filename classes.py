import abc, copy
import z3
import itertools
from instance_building_utils import *
Z3_HANDLED_TYPES = [z3.z3.ExprRef ,bool]
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

class ConditionList():
	def __init__(self, *args):
		#If any of the args are an AndList, flatten them
		self.args = self.flatten(args)
	def flatten(self,a):
		new_list = []
		for x in a:
			#If x a z3 expression, add it to the list
			z3_handleable = False
			for t in Z3_HANDLED_TYPES:
				if isinstance(x,t):
					z3_handleable = True
					new_list.append(x)
					break
			if not z3_handleable:
				if isinstance(x,type(self)):
					new_list.extend(self.flatten(x))
				else:
					print(type(x))
					raise TypeError("Don't know how to flatten {}".format(x))
					# new_list.extend(self.flatten(x))
		return new_list
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
	def to_z3(self):
		return z3.And(*self.args)


class OrList(ConditionList):
	def __init__(self, *args):
		super().__init__(*args)
		self.name = "OrList"
	def to_z3(self):
		return z3.Or(*self.args)

def test_AndList():
	z3_vars = []
	for i in range(10):
		z3_vars.append(z3.Bool(str(i)))
	a_correct = z3_vars[1:3]
	a = AndList(*z3_vars[1:3])
	# for x in a:
	# 	print(x)
	b_correct = z3_vars[:3]
	c_correct = z3_vars[4:6]
	d_correct = b_correct + c_correct
	b = AndList(z3_vars[0],a)
	c = AndList(*z3_vars[4:6])
	d = AndList(b,c)
	assert d.args == d_correct, "{}\n{}".format(d.args,d_correct)
	print("a:")
	for x in a.args:
		print(x)
	print("b:")
	for x in b.args:
		print(x)
	print("d")
	for x in d.args: print(x)

def test_OrList():
	pass

if __name__ == "__main__":
	test_AndList()