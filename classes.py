import abc, copy

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
