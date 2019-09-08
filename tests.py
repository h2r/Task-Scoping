import z3
import time
import pyrddl_inspector
from pyrddl.parser import RDDLParser
def test_reward_compilation():
	# Create a pyrddl ast whose conditions we know
	rddl_file_location = "./button-domains/button_sum_reward.rddl"
	with open(rddl_file_location, 'r') as file:
		rddl = file.read()
	# buid parser
	parser = RDDLParser()
	parser.build()
	# parse RDDL
	model = parser.parse(rddl)  # AST
	reward_ast = model.domain.reward
	groundings_from_top = dict()
	# solver =
	conditions_list = []
	reward_expr = pyrddl_inspector._compile_expression(reward_ast,)
if __name__ == "__main__":
	test_reward_compilation()