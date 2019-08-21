import abc, copy
import z3

def get_all_groundings(base_str, names, keys = None):
	if keys is None:
		keys = names.keys()
	groundings = []
	object_index_tuples = [[]]
	# Incorporate all arguments into the object index tuples
	for object_type in keys:
		new_object_index_tuples = []
		names_for_this_type = names[object_type]
		for partial_index_list in object_index_tuples:
			for i in names_for_this_type:
				extended_index_list = copy.deepcopy(partial_index_list)
				extended_index_list.append(str(i))
				new_object_index_tuples.append(extended_index_list)
		object_index_tuples = new_object_index_tuples
	for object_indices in object_index_tuples:
		indices_str = "_".join(object_indices)
		grounded_attribute_str = "{}_{}".format(base_str, indices_str)
		groundings.append(grounded_attribute_str)
	return groundings

class Skill(abc.ABC):
	def get_precondition(self):
		pass
	def get_action(self):
		pass
	def get_affected_variables(self):
		"""
		:return: list of affected vars. May modify to use forall
		"""
		pass

class SkillTriplet(Skill):
	def __init__(self, precondition, action, effect):
		"""
		:param precondition: Precondition object
		:param action: string
		:param effect: list of affected variables
		"""
		self.triplet = (precondition,action,effect)
	def get_precondition(self):
		return self.triplet[0]
	def get_action(self):
		return self.triplet[1]
	def get_affected_variables(self):
		return self.triplet[2]

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
			return self.name
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
	# def ground(self, object_names):
	# 	"""
	# 	:param object_counts: Dict[str, int]
	# 	:return: groundings of this attribute based on object_counts
	# 	"""
	# 	groundings = []
	# 	object_index_tuples = [[]]
	# 	# Incorporate all arguments into the object index tuples
	# 	for object_type in self.arguments:
	# 		new_object_index_tuples = []
	# 		names_for_this_type = object_names[object_type]
	# 		for partial_index_list in object_index_tuples:
	# 			for i in names_for_this_type:
	# 				extended_index_list = copy.deepcopy(partial_index_list)
	# 				extended_index_list.append(str(i))
	# 				new_object_index_tuples.append(extended_index_list)
	# 		object_index_tuples = new_object_index_tuples
	# 	for object_indices in object_index_tuples:
	# 		indices_str = "_".join(object_indices)
	# 		grounded_attribute_str = "{}_{}".format(self.name, indices_str)
	# 		groundings.append(grounded_attribute_str)
	# 	return groundings

class DomainAction(UngroundedThing):
	def __init__(self, name, arguments):
		super().__init__(name,arguments)
		# self.name = name
		# self.arguments = arguments
	# def ground(self,  object_names):

class AndList(list):
	def __init__(self, *args):
		#If any of the args are an AndList, flatten them
		self.args = self.flatten(args)
	def toConjunction(self):
		return z3.And(*self.args)
	def flatten(self,a):
		new_list = []
		for x in a:
			if hasattr(x,"__getitem__"):
				new_list = new_list + self.flatten(x)
			else:
				new_list.append(x)
		return new_list
	def __getitem__(self, item):
		return self.args[item]
	def __iter__(self):
		return self.args.__iter__()
	def __repr__(self):
		return str(self.args)
	def __str__(self):
		return self.__repr__()

def test_AndList():
	z3_vars = []
	for i in range(10):
		z3_vars.append(z3.Bool(str(i)))
	a = AndList(*z3_vars[1:3])
	for x in a:
		print(x)
	b = AndList(z3_vars[0],a)
	c = AndList(z3_vars[4:6])
	d = AndList(b,c)
	print("a:")
	for x in a.args:
		print(x)
	print("b:")
	for x in b.args:
		print(x)
	print("d")
	for x in d.args: print(x)

if __name__ == "__main__":
	test_AndList()