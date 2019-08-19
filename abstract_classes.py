import abc

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

class condition():
	"""
	A condition is a first order expression that defines a set of states in a domain
	"""
	def __init__(self, variables, z3_condition):
		self.variables = variables
		self.z3_condition = z3_condition
	def get_variables(self):
		return self.variables
	def get_z3(self, state):
		return self.z3_condition
