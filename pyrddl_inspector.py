from pyrddl.parser import RDDLParser
from pyrddl.expr import Expression
import itertools
import collections
import z3
from classes import *
from scoping import *
import instance_building_utils

att_name_to_domain_attribute = {}
all_object_names = {}
name_to_z3_var = {}
actions_list = []


def andlist_safe_or(*x):
	new_x = []
	for i in x:
		if isinstance(i,AndList):
			new_x.append(z3.And(*i.args))
		else:
			new_x.append(i)
	return z3.Or(*new_x)

def expr2slashyName(expr):
	return "{}/{}".format(expr.args[0],len(expr.args[1]))
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
	global actions_list
	# read RDDL file
	actions_list = rddl_model.domain.action_fluents.keys()
	print("actions_list:\n{}".format(actions_list))

	# print(type(model.domain.cpfs[1]))
	action_to_effect_to_precond = collections.defaultdict(lambda: collections.defaultdict(list))

	for state_variable_cpf in rddl_model.domain.cpfs[1]:
		if (state_variable_cpf.expr.etype[0] == 'control'):
			condition = state_variable_cpf.expr.args[0]
			false_case = state_variable_cpf.expr.args[2]
			if(false_case.etype[0] != 'control'):
				for action in actions_list:
					if action in condition.scope:
						action_to_effect_to_precond[action][state_variable_cpf.name.replace("'", "")].append(condition)
			else:
				while(false_case.etype[0] == 'control'):
					for action in actions_list:
						if action in condition.scope:
							action_to_effect_to_precond[action][state_variable_cpf.name.replace("'", "")].append(condition)
					
					# print(state_variable_cpf.expr)
					# print("CONDITION ==============================")
					# print(condition)
					# print("FALSE CASE ==============================")
					# print(false_case)
					# print("Temp break here!")
					condition = false_case.args[0]
					false_case = false_case.args[2]
					# print("CONDITION ==============================")
					# print(condition)
					# print("FALSE CASE ==============================")
					# print(false_case)
					# print("Temp break here!")

	# for state_variable_cpf in rddl_model.domain.cpfs[1]:
	# 	if (state_variable_cpf.expr.etype[0] == 'control'):
	# 		for action_precondition in state_variable_cpf.expr._expr[1]:
	# 			for action in actions_list:
	# 				if action in action_precondition.scope:
	# 					action_to_effect_to_precond[action][state_variable_cpf.name.replace("'", "")].append(action_precondition._expr)
	# 					print("Temporary Break!")

	return action_to_effect_to_precond

	# IMPORTANT!!!
	# This parser will only work for a transition function that begins with if statements for every block
	# Further, every block needs to contain statements with only one action => only one action allowed per time-step


# For every state predicate function, see which objects it takes in:
# Now, for every combination of those objects in the instance, make a proposition in z3
# Only set the proposition corresponding to the init-state to true!
def convert_to_z3(init_state, domain_objects, init_nonfluents, model_states, model_nonfluents, triplet_dict):
	global att_name_to_domain_attribute
	global all_object_names
	global name_to_z3_var
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
	att_name_to_domain_attribute = {}
	attribute_to_grounded_names = {}
	for att in attributes_list + constants:
		att_name_to_domain_attribute[att.name] = att
		grounded_attributes = att.ground(all_object_names)
		attribute_to_grounded_names[att.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			# Apply constraints
			pass

	# Converts the nonfluent constants to z3
	# constant_to_grounded_names = {}
	# for c in constants:
	# 	grounded_attributes = c.ground(all_object_names)
	# 	constant_to_grounded_names[c.name] = grounded_attributes
	# 	for g in grounded_attributes:
	# 		# Define var
	# 		name_to_z3_var[g] = c.type(g)
	# 		# Apply constraints
	# 		pass
	print("grounded atts:")
	for n in name_to_z3_var.keys():
		print(n)
	print("grounded atts over")

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

	skills_triplets = []
	for action in triplet_dict.keys():
		for effect in triplet_dict[action]:
			for precond in triplet_dict[action][effect]:
				print(precond)
				z3_expr = _compile_expression(precond)
				new_skill = SkillTriplet(z3_expr,action,effect)
				skills_triplets.append(new_skill)
				print("Temp break here!")
	return skills_triplets
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
		#'control': _compile_control_flow_expression,
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
	"""
	:param expr:
	:return: returns list of z3 vars, one for each possible set of arguments to the function
	"""

	# Return all groundings of this expression
	#TODO make sure this works for 0 arg pvars
	att_name = expr.etype[1]
	if expr2slashyName(expr) in actions_list:
		return True
	else:
		att = att_name_to_domain_attribute[att_name]
		#list of str
		all_att_groundings = att.ground(all_object_names)
		#list of z3 vars
		all_att_var_groundings = []
		all_att_var_groundings = [name_to_z3_var[g] for g in all_att_groundings]
		return all_att_var_groundings

	# return expr.scope
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
		if(isinstance(x, list)):
			if(len(x) > 1):
				# bool_in_z3 = AndList(*[op(x_elem) for x_elem in x])
				bool_in_z3 = [op(x_elem) for x_elem in x]
			else:
				bool_in_z3 = op(x[0])
		else:
			bool_in_z3 = op(x)

	else:
		etype2op = {
			'^': lambda x, y: AndList(*[x, y]),
			'&': lambda x, y: AndList(*[x, y]),
			'|': lambda x, y: andlist_safe_or(x, y),
			'=>': lambda x, y: andlist_safe_or(z3.Not(x), y),
			'<=>': lambda x, y: andlist_safe_or(z3.And(*[x, y]), z3.And(*[z3.Not(x), z3.Not(y)]))
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
# def _compile_control_flow_expression(expr: Expression):
# 	etype = expr.etype
# 	args = expr.args
# 	if etype[1] == 'if':
# 		condition = _compile_expression(args[0])
# 		true_case = _compile_expression(args[1])
# 		false_case = _compile_expression(args[2])
# 		# Compile the cases together sensibly with help from Michael!
# 		fluent = TensorFluent.if_then_else(condition, true_case, false_case)
# 	else:
# 		raise ValueError('Invalid control flow expression:\n{}'.format(expr))
# 	return fluent


def _compile_aggregation_expression(expr: Expression):
	etype = expr.etype
	args = expr.args

	typed_var_list = args[:-1]
	vars_list = [var for _, (var, _) in typed_var_list]
	expr2 = args[-1]

	compiled_expr = _compile_expression(expr2)

	# These functions in the values of the dict are incorrect, make sure to make them better. I have no clue
	# how to do this...
	etype2aggr = {
		# 'sum': x.sum,
		# 'prod': x.prod,
		# 'avg': x.avg,
		# 'maximum': x.maximum,
		# 'minimum': x.minimum,
		# 'exists': lambda x: z3.Or(*x),
		# 'forall': lambda x: AndList(*x)
		'exists': lambda x: andlist_safe_or(*x),
		'forall': lambda x: AndList(*x)
	}

	if etype[1] not in etype2aggr:
		raise ValueError('Invalid aggregation expression {}.'.format(expr))

	aggr = etype2aggr[etype[1]]
	fluent = aggr(compiled_expr)
	# fluent = aggr(vars_list=vars_list)

	return fluent


if __name__ == '__main__':
	# rddl_file_location = "/home/nishanth/Documents/IPC_Code/rddlsim/files/taxi-rddl-domain/taxi-oo_simple.rddl"
	# rddl_file_location = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
	rddl_file_location = "./misc-domains/button2.rddl"
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

	skill_triplets = convert_to_z3(initial_state, instance_objects, instance_nonfluents, model_states, model_non_fluents, test_dict)

	print("skills:")
	for s in skill_triplets: print(s)