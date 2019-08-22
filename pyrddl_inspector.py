from pyrddl.parser import RDDLParser
from pyrddl.expr import Expression
import itertools
import collections
import z3
from classes import *
from scoping import *
import instance_building_utils

def pull_state_var_dict(rddl_model):
	return rddl_model.domain.state_fluents


def pull_nonfluent_var_dict(rddl_model):
	return rddl_model.domain.non_fluents


def pull_instance_objects(rddl_model):
	return rddl_model.non_fluents.objects


def pull_init_nonfluent(rddl_model):
	return rddl_model.non_fluents.init_non_fluent


def pull_init_state(rddl_model):
	return rddl_model.instance.init_state


def make_triplet_dict(rddl_model):
	# read RDDL file
	actions_list = rddl_model.domain.action_fluents.keys()
	# print(actions_list)

	# print(type(model.domain.cpfs[1]))
	action_to_precond_to_effect = collections.defaultdict(lambda: collections.defaultdict(list))

	for state_variable_cpf in rddl_model.domain.cpfs[1]:
		if (state_variable_cpf.expr.etype[0] == 'control'):
			for action_precondition in state_variable_cpf.expr._expr[1]:
				for action in actions_list:
					if action in action_precondition.scope:
						print(state_variable_cpf.name.replace("'", ""))
						action_to_precond_to_effect[action][action_precondition._expr].append(
							state_variable_cpf.name.replace("'", ""))
	print(action_to_precond_to_effect)

	print('BREAK!')

	return action_to_precond_to_effect

	# IMPORTANT!!!
	# This parser will only work for a transition function that begins with if statements for every block
	# Further, every block needs to contain statements with only one action


# For every state predicate function, see which objects it takes in:
# Now, for every combination of those objects in the instance, make a proposition in z3
# Only set the proposition corresponding to the init-state to true!
def convert_to_z3(init_state, domain_objects, init_nonfluents, model_states, model_nonfluents, triplet_dict):
	# Makes a dict out of the state-variables like xpos=[x00,x01],ypos=[y00,y01]
	# These are already for the domain itself.
	all_object_names = {}
	for dom_obj in domain_objects:
		all_object_names[dom_obj[0]] = dom_obj[1]

	# Makes a list of the non-fluents (constants) from the domain
	constants = []
	for nonf in model_nonfluents:
		print(nonf)
		if (model_nonfluents[nonf].range == 'bool'):
			constants.append(DomainAttribute(model_nonfluents[nonf].name, z3.Bool, model_nonfluents[nonf].param_types))

	# Makes a list of all the attributes (state variables like passenger-in-taxi)
	attributes_list = []
	for state in model_states:
		if (model_states[state].range == 'bool'):
			attributes_list.append(DomainAttribute(model_states[state].name, z3.Bool, model_states[state].param_types))

	# Converts the attributes to z3 and assigns them to a dict
	name_to_z3_var = {}
	attribute_to_grounded_names = {}
	for att in attributes_list:
		grounded_attributes = att.ground(all_object_names)
		attribute_to_grounded_names[att.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			# Apply constraints
			pass

	# Converts the nonfluent constants to z3
	constant_to_grounded_names = {}
	for c in constants:
		grounded_attributes = c.ground(all_object_names)
		constant_to_grounded_names[c.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = c.type(g)
			# Apply constraints
			pass
	print("grojunded atts:")
	for n in name_to_z3_var.keys():
		print(n)
	print("grojunded atts over")

	# def ground2name(att_name, object_vals):
	# 	# print(att_name)
	# 	# print(object_vals)
	# 	name = att_name + "_" + "_".join([str(i) for i in object_vals])
	# 	return name
	#
	# def ground2var(att_name, object_vals, var_dict=name_to_z3_var):
	# 	return var_dict[ground2name(att_name, object_vals)]
	ground2name = instance_building_utils.g2n_names
	ground2var = instance_building_utils.g2v_builder(name_to_z3_var,ground2name)
	# Initialize a z3 solver to be returned when it contains the necessary z3 instantiation of z3 instances
	solver = z3.Solver()

	# Give the passenger, etc. their init values and push them into the solver
	for init_val in init_state:
		solver.add(ground2var(init_val[0][0], init_val[0][1]) == init_val[1])

	# Give all the initial non-fluents their values and push them into the solver
	for init_nonf in init_nonfluents:
		solver.add(ground2var(init_nonf[0][0], init_nonf[0][1]) == init_nonf[1])

	# print(solver.assertions)

	# TODO:
	# 1. Look into how to convert the preconditions to z3

	for action in triplet_dict.keys():
		for precond in triplet_dict[action].keys():
			curr_exp = precond
			print("BREAK!")

	# CODE WRITTEN BEFORE MICHAEL WROTE HIS CLASSES THAT MADE EVERYTHING CLEARER/BETTER!
	# list_of_list_of_propositions = []
	# for param_type in state.param_types:
	#     # Could speed this up with a dictionary, but trivial increase for now
	#     for instantiated_object in domain_objects:

	#     # For loop iterator
	#     #     if instantiated_object[0] == param_type:
	#     #         list_of_list_of_propositions.append(instantiated_object[1])
	#     # itertools.product(*list_of_list_of_propositions)


def _compile_expression(expr: Expression):
	etype2compiler = {
		'constant': _compile_constant_expression,
		'pvar': _compile_pvariable_expression,
		#        'randomvar':   _compile_random_variable_expression,
		#        'arithmetic':  _compile_arithmetic_expression,
		'boolean': _compile_boolean_expression,
		'relational': _compile_relational_expression,
		# These are functions like 'abs', etc. that we can handle later probably.
		# They don't appear in any of the domains that we care about.
		# 'func':        _compile_function_expression,
		'control': _compile_control_flow_expression,
		'aggregation': _compile_aggregation_expression
	}

	etype = expr.etype
	if etype[0] not in etype2compiler.keys():
		raise ValueError('Expression type unknown: {}'.format(etype))

	compiler_fn = etype2compiler[etype[0]]
	return compiler_fn(expr)


def _compile_constant_expression(expr: Expression):
	return expr.value


def _compile_pvariable_expression(expr: Expression):
	# If it's an action, we don't want it in the precondition. The
	# precondition is explicitly only over states
	# !!!!!!!!!!!!!!!CHECK!!!!!!!!!!!!!!!
	# IMPORTANT RETURN A Z3 VARIABLE FROM HAVING LOOKED IT UP IN THE Z3 NAME_TO_VAR DICT
	return expr.scope
	# etype = expr.etype
	# args = expr.args
	# name = expr._pvar_to_name(args)


def _compile_boolean_expression(expr: Expression):
	etype = expr.etype
	args = expr.args

	if len(args) == 1:
		etype2op = {
			'~': lambda x: z3.Not(x)
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid unary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0])
		bool_in_z3 = op(x)

	else:
		etype2op = {
			'^': lambda x, y: AndList([x, y]),
			'&': lambda x, y: AndList([x, y]),
			'|': lambda x, y: z3.Or(x, y),
			'=>': lambda x, y: z3.Or(z3.Not(x), y),
			'<=>': lambda x, y: z3.Or(AndList([x, y]), AndList([z3.Not(x), z3.Not(y)]))
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid binary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0])
		y = _compile_expression(args[1])
		bool_in_z3 = op(x, y)

	return bool_in_z3


# Done!
def _compile_relational_expression(expr: Expression):
	etype = expr.etype
	args = expr.args

	etype2op = {
		'<=': lambda x, y: x <= y,
		'<': lambda x, y: x < y,
		'>=': lambda x, y: x >= y,
		'>': lambda x, y: x > y,
		'==': lambda x, y: x == y,
		'~=': lambda x, y: x != y
	}

	if etype[1] not in etype2op:
		raise ValueError('Invalid relational expression:\n{}'.format(expr))

	op = etype2op[etype[1]]
	x = _compile_expression(args[0])
	y = _compile_expression(args[1])
	fluent = op(x, y)

	return fluent


# TODO: Finish this function!
# 1. Change the dictionary to be precond to effect to action
# 2. Rip out the precond and add the if/else preconds to the dict in place of the first precond
#
def _compile_control_flow_expression(expr: Expression):
	etype = expr.etype
	args = expr.args
	if etype[1] == 'if':
		condition = _compile_expression(args[0])
		true_case = _compile_expression(args[1])
		false_case = _compile_expression(args[2])
		# Compile the cases together sensibly with help from Michael!
		fluent = TensorFluent.if_then_else(condition, true_case, false_case)
	else:
		raise ValueError('Invalid control flow expression:\n{}'.format(expr))
	return fluent


# TODO: Fix this function to make it actually z3 worthy!
def _compile_aggregation_expression(expr: Expression):
	etype = expr.etype
	args = expr.args

	typed_var_list = args[:-1]
	vars_list = [var for _, (var, _) in typed_var_list]
	# type_list = [t for t,]
	expr = args[-1]

	x = _compile_expression(expr)

	# These functions in the values of the dict are incorrect, make sure to make them better. I have no clue
	# how to do this...
	etype2aggr = {
		'sum': x.sum,
		'prod': x.prod,
		'avg': x.avg,
		'maximum': x.maximum,
		'minimum': x.minimum,
		'exists': x.exists,
		'forall': x.forall
	}

	if etype[1] not in etype2aggr:
		raise ValueError('Invalid aggregation expression {}.'.format(expr))

	aggr = etype2aggr[etype[1]]
	fluent = aggr(vars_list=vars_list)

	return fluent


if __name__ == '__main__':
	# rddl_file_location = "/home/nishanth/Documents/IPC_Code/rddlsim/files/taxi-rddl-domain/taxi-oo_simple.rddl"
	rddl_file_location = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
	with open(rddl_file_location, 'r') as file:
		rddl = file.read()

	# buid parser
	parser = RDDLParser()
	parser.build()

	# parse RDDL
	model = parser.parse(rddl)  # AST
	test_dict = make_triplet_dict(model)
	model_states = pull_state_var_dict(model)
	model_non_fluents = pull_nonfluent_var_dict(model)
	instance_objects = pull_instance_objects(model)
	instance_nonfluents = pull_init_nonfluent(model)
	initial_state = pull_init_state(model)

	convert_to_z3(initial_state, instance_objects, instance_nonfluents, model_states, model_non_fluents, test_dict)