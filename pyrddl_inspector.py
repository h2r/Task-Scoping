from pyrddl.parser import RDDLParser
from pyrddl.expr import Expression
import itertools
import collections
import z3
from classes import *
import instance_building_utils
import pdb
from typing import List, Dict, Tuple
from utils import solver_implies_condition, get_iff, get_var_names, synth2varnames, AndList, not2

# att_name_to_domain_attribute = {}
all_object_names = {}
name_to_z3_var = {}
actions_list = []
pvar_to_param_types = {}
# synth2varnames = {}
#z3.get_var_names(z3 conditoimn)
#TODO rename reward_args, reward_params. Those are confusing names
#TODO Find out why we are getting if(button-on(b0),1,grandma(b0)) instead of if(button-on(b0),1,0)
def get_model_from_filepath(rddl_file_location):
	with open(rddl_file_location, 'r') as file:
		rddl = file.read()
	# buid parser
	parser = RDDLParser()
	parser.build()
	# parse RDDL
	model = parser.parse(rddl)  # AST
	return model

def expr2slashyName(expr):
	if(expr.args[1] is not None):
		return "{}/{}".format(expr.args[0],len(expr.args[1]))
	else:
		return "{}/{}".format(expr.args[0],0)

def pull_state_var_dict(rddl_model):
	return rddl_model.domain.state_fluents

def pull_nonfluent_var_dict(rddl_model):
	return rddl_model.domain.non_fluents


def pull_instance_objects(rddl_model):
	return rddl_model.non_fluents.objects


def pull_init_nonfluent(rddl_model):
	#TODO handle default values

	return rddl_model.non_fluents.init_non_fluent


def pull_init_state(rddl_model):
	#TODO handle default values
	return rddl_model.instance.init_state


def get_pvar_arg_types(pvar_name,rddl_model):
	for pvar in rddl_model.domain.pvariables:
		if pvar.name == pvar_name:
			return pvar.param_types
	raise KeyError("No pvar with name \"{}\" in rddl_model".format(pvar_name))

def get_all_objects_of_type(object_type, rddl_model):
	for x in rddl_model.non_fluents.objects:
		if x[0] == object_type:
			return x[1]
	raise KeyError("There are no objects of type {} in the rddl_model".format(object_type))

def get_all_sequences_of_objects(object_types, rddl_model):
	objects_by_type_list = [get_all_objects_of_type(t,rddl_model) for t in object_types]
	all_sequences = itertools.product(*objects_by_type_list)
	return all_sequences
def get_pvar_args_strings(pvar_name: str, expr: Expression) -> List[str]:
	"""
	:param att_name: name of pvar, ex. "toggle-button", "taxi-at"
	:param expr: the pyrddl.Expression object we are searching in
	:return: the strings used for the variable arguments in the pvar, ex. "?x". Returns the first found strings.
	Meant to be used when the pvar is an action, and thus would only be found once.
	Returns [] if the pvar is not found
	"""
	# if isinstance(expr, CPF)
	#Search through expr, its args, etc.
	# if pvar_name == "move_west":
	# 	print("westward, ho")
	# if isinstance(expr.args,int):
	# 	print("int ya boii")

	# if(pvar_name == "toggle_blinker" or pvar_name == "move_west"):
	# 	pdb.set_trace()

	for arg_id in range(len(expr.args)):
		if isinstance(expr.args[arg_id],Expression):
			if expr.args[arg_id].etype[0] == 'constant': return []
			x = get_pvar_args_strings(pvar_name,expr.args[arg_id])
			if x is None:
				return []
			if len(x) > 0:
				return x
		elif isinstance(expr.args[arg_id],str):
			if expr.args[arg_id] == pvar_name:
				if(expr.args[arg_id + 1] is None):
					return []
				else:
					return expr.args[arg_id + 1]

	return []

def plugin_objects_to_pvar(pvar_name,pvar_parameters,groundings):
	"""
	:param pvar_name: name of pvar, ex. "toggle-button"
	:param pvar_parameters: list of strings for variable parameters, ex. ["?b"]
	:param groundings: dictionary that maps variable parameters to object names. Ex {"?b": "b0"}
	:return: pvar applied to the object names. Ex "toggle-button(b0)" (this example assumes g2n has not changed)
	"""
	object_names = []
	# if(pvar_name == "move_north"):
	# 	pdb.set_trace()
	try:
		for p in pvar_parameters:
			object_names.append(groundings[p])
	except:
		# pdb.set_trace()
		pass

	return instance_building_utils.g2n_names(pvar_name,object_names)

# def get_possible_groundings(pvar_name, variable_param_strings, known_groundings):
# 	groundings_by_param = []
# 	for vps in variable_param_strings:
# 		# If the variable is defined at the top of the cpf, we have already determined it's value
# 		if vps in known_groundings.keys():
# 			groundings_by_param.append([known_groundings[vps]])
# 		# Otherwise, it can be any object of the correct type
# 		else:
# 			param_type = pvar_to_param_types[pvar_name]
# 			groundings_by_param.append(all_object_names[param_type])
# 	return groundings_by_param
def get_grounding_dict_pairs(variable_param_strings: List[str],groundings_by_param: List[List[str]]) -> List[Tuple[Tuple[str,...],Dict[str,str]]]:
	"""
	:param variable_param_strings: list of strings of parameters, ex ["?p1,"?t0"]
	:param groundings_by_param: List of possible groundings for each param, aligned with variable_param_strings
		ex. [["p0","p1"],["t0"]}
	:return: List of pairs, where pair[0] is a list containing a single object from each lisst in groundings_by_param
		and pair[1] is a dictionary that maps from variable_param_strings to the object name it was replaced with in pair[0]
	"""
	total_groundings_no_dict = itertools.product(*groundings_by_param)
	total_groundings_dict_pairs = []
	for tg_id, tg in enumerate(total_groundings_no_dict):
		#Make grounding dict
		grounding_dict = {}
		for arg_place, arg in enumerate(tg):
			variable_param_str = variable_param_strings[arg_place]
			grounding_dict[variable_param_str] = arg
		total_groundings_dict_pairs.append((tg,grounding_dict))
	return total_groundings_dict_pairs
def get_goal_conditions_from_reward(reward, reward_parameters, solver):
	"""
	:param reward: z3 function var corresponding to the rddl reward.
	:param reward_parameters: list of z3 conditions mentioned in reward, in order
	:param solver: z3 Solver with reward function and constants asserted
	:return:
	"""
	goal_conditions = []
	for c_id in range(len(reward_parameters)):
		if isinstance(reward_parameters[c_id],z3.BoolRef):
			#Check if c True makes reward higher, c False makes reward higher, or unknown. We assume the condition matters, otherwise its poorly defined
			reward_args_true_c = [reward_parameters[i] if i != c_id else True for i in range(len(reward_parameters))]
			reward_args_false_c = [reward_parameters[i] if i != c_id else False for i in range(len(reward_parameters))]
			#These conditions are, respectively, c always being good for reward, c always being bad for reward
			c_is_goal = (reward(*reward_args_true_c) >= reward(*reward_parameters))
			not_c_is_goal = (reward(*reward_args_false_c) >= reward(*reward_parameters))
			# print("assertions for {}: {}".format(c_id,solver.assertions))
			if solver_implies_condition(solver, c_is_goal):
				goal_conditions.append(reward_parameters[c_id])
			elif solver_implies_condition(solver,not_c_is_goal):
				goal_conditions.append(z3.Not(reward_parameters[c_id]))
	return goal_conditions

def get_reward_conditions(rddl_model, solver=None):
	"""
	:param rddl_model:
	:param solver: solver with constant values asserted
	:return: list of conditions mentioned in z3 reward function, list of pvars mentioned in the reward function outside of conditions, z3 func representing reward function
	"""
	reward_expr = rddl_model.domain.reward

	if False and (reward_expr.etype[0] == 'control'):
		condition = reward_expr.args[0]
		compiled_reward = _compile_expression(condition,dict(),solver)
		# compiled_reward = and2()
		return z3.And(compiled_reward)  #TODO Why are we passing a single arg? Should't we a;ways pass multiple
	else:
		#Assume the reward is a sum of sums, or at least has no ifs
		grounding_dict = dict()
		reward_params = []
		reward_args = {
			"conditions_list":[],
			"unscopable_pvars":[],
			"synthetic_conditions":[],
			"reward_function_parameters":reward_params,
			"in_condition":False
		}
		#TODO figure out why button-on(bi) is being put in unscopable_pvars and conditions_list/synthetic_conditions, so is duplicated in reward_function_parameters
		compiled_reward = _compile_expression(reward_expr,grounding_dict,solver,reward_args=reward_args)
		
		for c in reward_args["conditions_list"]: print(c)
		#We need to separate pvars that occur only in conditions from pvars that occur outside of conditions.
		#We can do this by passing in an unconditions_pvars list to _compile_expression
		print("reward got")
		#TODO return only the relevant conditions, and also the list of pvars we definitely care about
		#TODO create function. To get signature right, we need to know how to put together synthetic_conditions and unscopable_pvars.
		#TODO Easiest way is to create another list for the parameters, and add conditions and pvars to this list as we recurse. Then get types of this lists elements
		# reward_func = z3.Function('reward_func',)
		reward_signature = [x.sort() for x in reward_params] + [z3.RealSort()] #Consider changing to IntSort() if that makes this faster
		reward_function = z3.Function('reward_function',reward_signature)
		reward_definition = z3.ForAll(reward_params,reward_function(*reward_params) == compiled_reward)
		solver.add(reward_definition)
		goal_conditions = get_goal_conditions_from_reward(reward_function,reward_params,solver)
		print("Got Goal conditions")

		return goal_conditions, reward_args["unscopable_pvars"]


def reward_to_z3_function(reward_ast, solver):
	"""
	:param reward_ast: the ast of the reward functionje
	:param solver: z3.Solver object we will push the reward function to
	:return: a z3 function object corresponding to the reward, a list of conditions corresponding to the arguments of the reward function
	"""
	pass

def make_triplet_dict(rddl_model, type2names):
	"""
	:param rddl_model:
	:param type2names:
	:param ground2name: takes in attribute name and list of object names, and returns a str of the grounded att
	:return: Dict of form [grounded_action][grounded_pvar] -> (condition ast, grounding dictionary)
	"""
	global actions_list
	global pvar_to_param_types
	# read RDDL file
	actions_list = rddl_model.domain.action_fluents.keys()
	print("actions_list:\n{}".format(actions_list))
	#Get grounded actions

	# print(type(model.domain.cpfs[1]))
	action_to_effect_to_precond = collections.defaultdict(lambda: collections.defaultdict(list))

	for state_variable_cpf in rddl_model.domain.cpfs[1]:
		#Get state variable name by removing the "'" suffix
		state_variable_name = state_variable_cpf.pvar[1][0][:-1]
		#Get strings used as arguments for pvar
		arg_strings_ungrounded = state_variable_cpf.pvar[1][1]
		#Get arg types of this pvar
		arg_types = get_pvar_arg_types(state_variable_name,rddl_model)
		pvar_to_param_types[state_variable_name] = arg_types
		#Get all sequences of objects that can be used as arguments for this pvar
		all_possible_arg_lists = list(get_all_sequences_of_objects(arg_types,rddl_model))
		#For each sequence of args, ground this pvar and create a skill
		for current_arg_list in all_possible_arg_lists:
			#Ground state_variable to current_arg_list
			grounded_state_variable = g2n_names(state_variable_name,current_arg_list)
			#Make the grounding dictionary we will pass down the recursive compilation chain
			groundings_from_top = {}
			for arg_id in range(len(arg_strings_ungrounded)):
				groundings_from_top[arg_strings_ungrounded[arg_id]] = current_arg_list[arg_id]
			
			if (state_variable_cpf.expr.etype[0] == 'control'):
				condition = state_variable_cpf.expr.args[0]
				false_case = state_variable_cpf.expr.args[2]
				nested_conds = True
				once_more = False

				# What's going on in this loop?:
				# 1. No matter what, the 'for action' loop needs to execute once for the current
				# condition variable
				# 2. If this is a nested condition, then the overall while loop needs to execute 
				# once more than otherwise, so once_more is set to True
				# 3. Else, if it's not, then there's no more nested conditions to hit and the loop 
				# can just terminate
				
				while(nested_conds):
					
					for action in actions_list:
							if action in condition.scope:
								#Ground the action based on groundings_from_top.
								cleaned_action_name = action.split("/")[0]
								action_variable_args = get_pvar_args_strings(cleaned_action_name, condition)
								grounded_action_str = plugin_objects_to_pvar(cleaned_action_name,action_variable_args,groundings_from_top)
								condition_grounding_pair = (condition,groundings_from_top)
								#Add to the dictionary.
								action_to_effect_to_precond[grounded_action_str][grounded_state_variable].append(condition_grounding_pair)
					
					if (false_case.etype[0] == 'control'):
						condition = false_case.args[0]
						false_case = false_case.args[2]
						once_more = True
					else:
						if(once_more):
							once_more = False
						else:
							nested_conds = False

	return action_to_effect_to_precond

# For every state predicate function, see which objects it takes in:
# Now, for every combination of those objects in the instance, make a proposition in z3
# Only set the proposition corresponding to the init-state to true!
def convert_to_z3(rddl_model):
	global att_name_to_domain_attribute
	global all_object_names
	global name_to_z3_var

	# Makes a dict out of the state-variables like xpos=[x00,x01],ypos=[y00,y01]
	# These are already for the domain itself.
	model_states = pull_state_var_dict(rddl_model)
	model_nonfluents = pull_nonfluent_var_dict(rddl_model)
	domain_objects = pull_instance_objects(rddl_model)

	all_object_names = {}
	for dom_obj in domain_objects:
		all_object_names[dom_obj[0]] = dom_obj[1]
	print("all_object_names:")
	for k,v in all_object_names.items(): print("{}: {}".format(k,v))
	# Makes a list of the non-fluents (constants) from the domain
	att_name_to_domain_attribute = {}
	rddl2z3_sorts = {
		"bool":z3.Bool,
		"int":z3.Int,
		"real":z3.Real
	}

	#TODO when and why do I use each of these?
	# A solver that contains all information about the start state. Used by the scoping algorithm
	solver = z3.Solver()
	# A solver that contains only constant assertions. Used for ...
	solver_constants_only = z3.Solver()
	init_nonfluents = pull_init_nonfluent(rddl_model)
	init_state = pull_init_state(rddl_model)

	# ground2name = instance_building_utils.g2n_names
	def initialize_variables(pvars_dict,init_values_list,name_to_z3_var,solvers_list):
		#TODO make sure this works for pvars with no arguments
		init_values_dict = collections.defaultdict(lambda: collections.defaultdict(lambda: None))
		for (pvar, args_list), val in init_values_list:
			if args_list is None:
				args_list = []
			init_values_dict[pvar][tuple(args_list)] = val
		constants = []
		for pvar_name, pvar in pvars_dict.items():
			print(pvar_name)
			rddl_range = pvar.range
			z3_sort = rddl2z3_sorts[rddl_range]
			# constants.append(DomainAttribute(pvar.name, z3_sort, pvar.param_types))
			# Assert constant values.
			# Get all possible args to the pvar
			param_types = pvar.param_types
			if param_types is None: param_types = []
			argument_product_space = [all_object_names[x] for x in param_types]
			all_possible_arg_lists = itertools.product(*argument_product_space)
			#Create z3_vars
			for args_list in all_possible_arg_lists:
				#Declare z3 var
				grounded_name = g2n_names(pvar.name, args_list)
				z3_var = rddl2z3_sorts[rddl_range](grounded_name)
				name_to_z3_var[grounded_name] = z3_var
					# grounded_attributes = att.ground(all_object_names)
				# attribute_to_grounded_names[att.name] = grounded_attributes
				val = init_values_dict[pvar.name][tuple(args_list)]
				if val is None:
					val = pvar.default
				for s in solvers_list:
					s.add(z3_var == val)
		# Add to solvers
	#TODO add default values for pvars

	initialize_variables(model_nonfluents,init_nonfluents,name_to_z3_var,[solver,solver_constants_only])
	initialize_variables(model_states,init_state,name_to_z3_var,[solver])
	name_to_z3_var_copy = name_to_z3_var
	for k,v in name_to_z3_var.items(): print(k)
	# ground2var = instance_building_utils.g2v_builder(name_to_z3_var,ground2name)

	# Makes a list of all the attributes (state variables like passenger-in-taxi)
	# attributes_list = []
	# for state in model_states:
	# 	rddl_range = model_states[state].range
	# 	z3_sort = rddl2z3_sorts[rddl_range]
	# 	attributes_list.append(DomainAttribute(model_states[state].name, z3_sort, model_states[state].param_types))
			# att_name_to_domain_attribute[model_states[state].name] = model_states[state].args_names

	# Converts the attributes to z3 and assigns them to a dict
	# att_name_to_arg_names = {}
	# name_to_z3_var = {}
	# attribute_to_grounded_names = {}
	# for att in attributes_list + constants:
	# 	# att_name_to_domain_attribute[att.name] = att
	# 	if att.arguments is None or len(att.arguments) == 0:
	# 		grounded_attributes = [g2n_names(att.name,[])]
	# 	else:
	# 		grounded_attributes = att.ground(all_object_names)
	# 	attribute_to_grounded_names[att.name] = grounded_attributes
	# 	for g in grounded_attributes:
	# 		# Define var
	# 		name_to_z3_var[g] = att.type(g)
	# 		# Apply constraints
	# 		pass

	print("grounded atts:")
	for n in name_to_z3_var.keys():
		print(n)
	print("grounded atts over")

	# Initialize a z3 solver to be returned when it contains the necessary z3 instantiation of z3 instances

	# Give the passenger, etc. their init values and push them into the solver
	# for init_val in init_state:
	# 	solver.add(ground2var(init_val[0][0], init_val[0][1]) == init_val[1])
	# # Give all the initial non-fluents their values and push them into the solver
	# for init_nonf in init_nonfluents:
	# 	att_name = init_nonf[0][0]
	# 	obj_names = init_nonf[0][1]
	# 	if obj_names is None:
	# 		obj_names = []
	# 	solver.add(ground2var(att_name, obj_names) == init_nonf[1])
	# 	solver_constants_only.add(ground2var(att_name, obj_names) == init_nonf[1])
	# reward_ast = get_reward_conditions(rddl_model, solver_constants_only)
	#TODO why do we use solver_constants_only here?
	goal_conditions, necessarily_relevant_pvars = get_reward_conditions(rddl_model, solver_constants_only)
	triplet_dict = make_triplet_dict(rddl_model, all_object_names)

	skills_triplets = []
	action_effect_precond_list = []
	for action in triplet_dict.keys():
		for effect in triplet_dict[action]:
			for precond in triplet_dict[action][effect]:
				# solver_constants_only used here because we don't want the initial condition 
				# to be assumed true when we compile actions
				if((action, effect, precond) not in action_effect_precond_list):
					action_effect_precond_list.append((action,effect,precond))
					z3_expr = _compile_expression(*precond,solver_constants_only)
					if(action == "pickup(p0)"):
						pass
						# print("~~~")
						# print(type(effect))
						# print("~~~")
						# pdb.set_trace()
					new_skill = Skill(z3_expr, action, [effect])
					skills_triplets.append(new_skill)

	# pdb.set_trace()
	return skills_triplets, goal_conditions, necessarily_relevant_pvars, solver

def _compile_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, reward_args=None):
	global synth2varnames
	etype2compiler = {
		'constant': _compile_constant_expression,
		'pvar': _compile_pvariable_expression,
		'randomvar':   _compile_random_variable_expression,
		'arithmetic':  _compile_arithmetic_expression,
		'boolean': _compile_boolean_expression,
		'relational': _compile_relational_expression,
		# These are functions like 'abs', etc. that we can handle later probably.
		# They don't appear in any of the domains that we care about.
		# 'func':        _compile_function_expression,
		'control': _compile_control_flow_expression,
		'aggregation': _compile_aggregation_expression
	}
	
	etype = expr.etype

	compiler_type, compiler_subtype = etype
	if compiler_type not in etype2compiler.keys():
		raise ValueError('Expression type unknown: {}'.format(etype))
	compiler_fn = etype2compiler[compiler_type]
	#if we are compiling a reward expression
	if reward_args is not None:
		#We copy the reward_args dictionary so that in_condition is only changed for the descendents of this function call.
		#The copy is shallow because we want the compilation to edit an existing list, so we must pass the lists by reference
		#in_condition is the only variable in reward_args that we don't want to pass by reference, and this is the only place
		#it is modified, so this should be safe. If there is a bug, it's probably here.
		reward_args = copy.copy(reward_args)
		in_condition_old = reward_args["in_condition"]
		
		# If the compiler_type is one of the following, then the result will be a condition, so we set in_condition=True
		# Some pvars or constants are also conditions, but in those cases there will be no sub-conditions, so we don't need to set in_condition
		# that doesn't seem worth the extra code

		condition_compiler_types = ['boolean', 'relational', 'aggregation']
		if compiler_type in condition_compiler_types and compiler_subtype != 'sum':
			reward_args["in_condition"] = True
	else: in_condition_old = None
	new_expr = compiler_fn(expr,groundings_from_top,solver_constants_only,reward_args)

	#If we are gathering conditions and we are not yet in a condition
	# Dictionary mapping from synthetic variable string to the original variable. Needed for get_var_names()
	if reward_args is not None:
		if in_condition_old == False:
			#If the new expression is a condition, add it to the list
			#and2s are a pain. We should really find a way to decompose conjunctions instead of storing and2s
			new_conditions = []
			if isinstance(new_expr,AndList):
				raise TypeError(f"AndList: {new_expr}")
				new_conditions = new_expr.args
			elif isinstance(new_expr,z3.z3.BoolRef):
				new_conditions = [new_expr]
			for x in new_conditions:
				reward_args["conditions_list"].append(x)
				#If x is a z3 var, add it to synthetic_conditions. Else, create a new var to represent the condition and add it
				if x.num_args() == 0:
					new_parameter = x
				else:
					new_parameter = z3.Bool("synth_{}".format(x))
					synth2varnames[str(new_parameter)] = get_var_names(x)
					solver_constants_only.add(get_iff(new_parameter,x))
				reward_args["synthetic_conditions"].append(new_parameter)
				reward_args["reward_function_parameters"].append(new_parameter)
	return new_expr
def _compile_control_flow_expression(expr: Expression, grounding_dict:Dict[str,str],solver_constants_only, reward_args=None):
	compiler_type, compiler_subtype = expr.etype
	args = expr.args
	if compiler_subtype == "if":
		condition = _compile_expression(args[0], grounding_dict, solver_constants_only, reward_args)
		if isinstance(condition,AndList):
			raise TypeError(f"AndList: {condition}")
			condition = condition.to_z3()
		true_case = _compile_expression(args[1], grounding_dict, solver_constants_only, reward_args)
		false_case = _compile_expression(args[2], grounding_dict, solver_constants_only, reward_args)
		return z3.If(condition,true_case,false_case)
	else:
		raise ValueError('Invalid control flow expression:\n{}'.format(expr))

def _compile_constant_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only , reward_args=None):
	return expr.value

def _compile_arithmetic_expression(expr: Expression, grounding_dict:Dict[str,str],solver_constants_only, reward_args=None):
		etype = expr.etype
		args = expr.args

		if len(args) == 1:
			etype2op = {
				'+': lambda x: x,
				'-': lambda x: -x
			}

			if etype[1] not in etype2op:
				raise ValueError('Invalid binary arithmetic expression:\n{}'.format(expr))

			op = etype2op[etype[1]]
			x = _compile_expression(args[0], grounding_dict, reward_args)
			fluent = op(x)

		else:
			etype2op = {
				'+': lambda x, y: x + y,
				'-': lambda x, y: x - y,
				'*': lambda x, y: x * y,
				'/': lambda x, y: x / y,
			}

			if etype[1] not in etype2op:
				raise ValueError('Invalid binary arithmetic expression:\n{}'.format(expr))

			op = etype2op[etype[1]]
			x = _compile_expression(args[0], grounding_dict,solver_constants_only, reward_args)
			y = _compile_expression(args[1], grounding_dict,solver_constants_only, reward_args)
			#Make sure we are adding numbers, not bools
			if isinstance(x,z3.BoolRef):
				x = z3.If(x,1,0)
			if isinstance(y,z3.BoolRef):
				y = z3.If(y,1,0)
			fluent = op(x, y)

		return fluent

def _compile_pvariable_expression(expr: Expression, grounding_dict: Dict[str, str],solver_constants_only, reward_args=None):
	"""
	:param expr:
	:return: returns a z3 expr with the specified groundings
	"""

	# Return all groundings of this expression
	#TODO make sure this works for 0 arg pvars
	pvar_name, variable_param_strings = expr.args
	# if pvar_name == "PASSENGERS_YOU_CARE_FOR":
	# 	print("BREAK")
	if expr2slashyName(expr) in actions_list:
		return True
	else:
		if variable_param_strings is None:
			variable_param_strings = []
		object_names = [grounding_dict[x] for x in variable_param_strings]
		z3_var = name_to_z3_var[instance_building_utils.g2n_names(pvar_name,object_names)]
		if reward_args is not None and not reward_args["in_condition"]:
			# If it is a bool, it is a condition and will be processed by the parent _compile_expression
			# Otherwise, it is unscopable and we must deal with it here
			if not isinstance(z3_var,z3.BoolRef):
				reward_args["unscopable_pvars"].append(z3_var)
				reward_args["reward_function_parameters"].append(z3_var)
		return z3_var

def _compile_boolean_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, reward_args=None):
	etype = expr.etype
	args = expr.args

	if len(args) == 1:
		etype2op = {
			'~': lambda x: not2(x)
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid unary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0], groundings_from_top,solver_constants_only, reward_args)
		if(isinstance(x, list)):
			if(len(x) > 1):
				# bool_in_z3 = and2(*[op(x_elem) for x_elem in x])
				bool_in_z3 = [op(x_elem) for x_elem in x]
			else:
				bool_in_z3 = op(x[0])
		else:
			bool_in_z3 = op(x)

	else:
		etype2op = {
			'^': lambda x, y: z3.And(*[i for i in [x, y] if not (i is True)]),
			'&': lambda x, y: z3.And(*[i for i in [x, y] if not (i is True)]),
			'|': lambda x, y: z3.Or(x, y, solver=solver_constants_only),
			'=>': lambda x, y: z3.Or(z3.Not(x), y),
			# '<=>': lambda x, y: or2(z3.And(*[x, y]), z3.And(*[z3.Not(x), z3.Not(y)]))
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid binary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0],groundings_from_top,solver_constants_only, reward_args)
		y = _compile_expression(args[1],groundings_from_top,solver_constants_only, reward_args)
		bool_in_z3 = op(x, y)

	return bool_in_z3


def _compile_relational_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, reward_args=None):
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
	x = _compile_expression(args[0],groundings_from_top,solver_constants_only, reward_args)
	y = _compile_expression(args[1],groundings_from_top,solver_constants_only, reward_args)
	fluent = op(x, y)

	return fluent

def _compile_random_variable_expression(self,
											expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, reward_args=None):
		etype = expr.etype
		args = expr.args
		
		if etype[1] == 'Bernoulli':
			return True

			# mean = self._compile_expression(args[0], scope, batch_size, noise)
			# dist, sample = TensorFluent.Bernoulli(mean, batch_size)
		# elif etype[1] == 'Uniform':
		#     if noise is None:
		#         low = self._compile_expression(args[0], scope, batch_size, noise)
		#         high = self._compile_expression(args[1], scope, batch_size, noise)
		#         dist, sample = TensorFluent.Uniform(low, high, batch_size)
		#     else:
		#         xi = noise.pop()
		#         # xi = TensorFluent(xi, scope=[], batch=True)
		#         xi = TensorFluent(tf.sigmoid(xi), scope=[], batch=True) # squashed noise
		#         low = self._compile_expression(args[0], scope, batch_size, noise)
		#         high = self._compile_expression(args[0], scope, batch_size, noise)
		#         sample = low + (high - low) * xi

		# elif etype[1] == 'Normal':
		#     if noise is None:
		#         mean = self._compile_expression(args[0], scope, batch_size, noise)
		#         variance = self._compile_expression(args[1], scope, batch_size, noise)
		#         dist, sample = TensorFluent.Normal(mean, variance, batch_size)
		#     else:
		#         xi = noise.pop()
		#         # xi = TensorFluent(xi, scope=[], batch=True)
		#         xi = TensorFluent(2.0 * tf.tanh(xi / 2.0), scope=[], batch=True) # squashed noise
		#         mean = self._compile_expression(args[0], scope, batch_size, noise)
		#         variance = self._compile_expression(args[1], scope, batch_size, noise)
		#         sample = mean + TensorFluent.sqrt(variance) * xi
		# elif etype[1] == 'Laplace':
		#     mean = self._compile_expression(args[0], scope, batch_size, noise)
		#     variance = self._compile_expression(args[1], scope, batch_size, noise)
		#     dist, sample = TensorFluent.Laplace(mean, variance, batch_size)
		# elif etype[1] == 'Gamma':
		#     shape = self._compile_expression(args[0], scope, batch_size, noise)
		#     scale = self._compile_expression(args[1], scope, batch_size, noise)
		#     dist, sample = TensorFluent.Gamma(shape, scale, batch_size)
		# elif etype[1] == 'Exponential':
		#     if noise is None:
		#         rate = self._compile_expression(args[0], scope, batch_size, noise)
		#         dist, sample = TensorFluent.Exponential(rate, batch_size)
		#     else:
		#         xi = noise.pop()
		#         # xi = TensorFluent(xi, scope=[], batch=True)
		#         xi = TensorFluent(tf.sigmoid(xi), scope=[], batch=True) # squashed noise
		#         rate = self._compile_expression(args[0], scope, batch_size, noise)
		#         sample = - (TensorFluent.constant(1.0) / rate) * TensorFluent.log(xi)
		else:
			raise ValueError('Invalid random variable expression:\n{}.'.format(expr))

		# return sample

def _compile_aggregation_expression(expr: Expression, grounding_dict: Dict[str,str],solver_constants_only, reward_args=None):
	etype2aggr = {
		'sum': lambda x: z3.Sum(x),
		# 'prod': x.prod,
		# 'avg': x.avg,
		# 'maximum': x.maximum,
		# 'minimum': x.minimum,
		'exists': lambda x: z3.Or(*x),
		'forall': lambda x: z3.And(*[i for i in x if not (i is True)])
	}
	etype = expr.etype
	args = expr.args
	typed_vars_list = args[:-1]
	new_params = [v[1] for v in typed_vars_list]
	expr2compile = args[-1]
	compiled_expressions = []
	aggr = etype2aggr[etype[1]]

	#Get all groundings of new params
	possible_objects_by_param = []
	new_params_names = []
	for param_name, param_type in new_params:
		possible_objects_by_param.append(all_object_names[param_type])
		new_params_names.append(param_name)
	possible_argument_sequences = itertools.product(*possible_objects_by_param)
	for arg_sequence in possible_argument_sequences:
		new_grounding_dict = copy.copy(grounding_dict)
		for param_id, object_name in enumerate(arg_sequence):
			param_name = new_params[param_id][0]
			new_grounding_dict[param_name] = object_name
		#Get z3 expression
		new_expr = _compile_expression(expr2compile, new_grounding_dict,solver_constants_only,reward_args)
		compiled_expressions.append(new_expr)
	if etype[1] == "sum":
		numberized_compiled_expressions = []
		for c in compiled_expressions:
			if isinstance(c,z3.BoolRef):
				numberized_compiled_expressions.append(z3.If(c,1,0))
				# if not reward_args["in_condition"]:
				# 	# The pvar was added to both unscopable_pvars and conditions_list. It should only have been added to conditions_list
				# 	reward_args["unscopable_pvars"].remove(c)
				# 	reward_args["reward_function_parameters"].remove(c)
				# 	# reward_args["conditions_list"].append(c)
			else:
				numberized_compiled_expressions.append(c)
		compiled_expressions = numberized_compiled_expressions

	#Apply aggregator
	return aggr(compiled_expressions)


def test_get_pvar_args_strings():
	rddl_file_location = "./button-domains/buttons_two-arg_pvar.rddl"
	model = get_model_from_filepath(rddl_file_location)
	pvar_args_strings_true = ["?b"]
	cpfs =  model.domain.cpfs[1]
	action_name = "toggle-button"
	for c in cpfs:
		condition = c.expr.args[0]
		pvar_args_strings_empirical = get_pvar_args_strings(action_name,c.expr)
		assert pvar_args_strings_true == pvar_args_strings_empirical, "{}\n{}".format(pvar_args_strings_true,pvar_args_strings_empirical)

def prepare_rddl_for_scoper(rddl_file_location):
		with open(rddl_file_location, 'r') as file:
			rddl = file.read()

		# buid parser
		parser = RDDLParser()
		parser.build()

		# parse RDDL
		model = parser.parse(rddl)  # AST

		skill_triplets, goal_conditions, necessarily_relevant_pvars, solver = convert_to_z3(model)

		return goal_conditions, necessarily_relevant_pvars, skill_triplets, solver

if __name__ == '__main__':
		# rddl_file_location = "/home/nishanth/Documents/IPC_Code/rddlsim/files/taxi-rddl-domain/taxi-oo_simple.rddl"
		# rddl_file_location = "./taxi-rddl-domain/taxi-oo_mdp_composite_01.rddl"
		# rddl_file_location = "./taxi-rddl-domain/taxi-structured-composite_01.rddl"
		# rddl_file_location = "./taxi-rddl-domain/taxi-structured-deparameterized_actions.rddl"
		# rddl_file_location = "./button-domains/2buttons3atts.rddl"
		# rddl_file_location = "./button-domains/2buttons4atts.rddl"
		# rddl_file_location = "./button-domains/buttons_two-arg_pvar.rddl"
		rddl_file_location = "./misc-domains/academic-advising_composite_01.rddl"
		with open(rddl_file_location, 'r') as file:
			rddl = file.read()

		# buid parser
		parser = RDDLParser()
		parser.build()

		# parse RDDL
		rddl_model = parser.parse(rddl)  # AST
	#	test_dict = make_triplet_dict(model)

		skill_triplets, goal_conditions, necessarily_relevant_pvars, solver = convert_to_z3(rddl_model)
		print("skills:")
		for s in skill_triplets: print(s)