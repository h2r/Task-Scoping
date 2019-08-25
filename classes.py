import copy
from abc import ABC
import z3
import itertools
from instance_building_utils import *


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


if __name__ == "__main__":
	test_AndList()
	test_ConditionList()