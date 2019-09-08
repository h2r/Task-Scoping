from pyrddl.parser import RDDLParser
from pyrddl.expr import Expression
import itertools
import collections
import z3
from classes import *
import instance_building_utils
from typing import List, Dict, Tuple
from logic_utils import solver_implies_condition, check_implication, or2, and2, AndList, OrList
att_name_to_domain_attribute = {}
all_object_names = {}
name_to_z3_var = {}
actions_list = []
pvar_to_param_types = {}
#z3.get_var_names(z3 conditoimn)
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
	for arg_id in range(len(expr.args)):
		if isinstance(expr.args[arg_id],Expression):
			if expr.args[arg_id].etype[0] == 'constant': return []
			x = get_pvar_args_strings(pvar_name,expr.args[arg_id])
			if x is None:
				# print("Nani!???")
				return []
			if len(x) > 0:
				return x
		elif isinstance(expr.args[arg_id],str):
			if expr.args[arg_id] == pvar_name:
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
	for p in pvar_parameters:
		object_names.append(groundings[p])
	return instance_building_utils.g2n_names(pvar_name,object_names)

def get_possible_groundings(pvar_name, variable_param_strings, known_groundings):
	groundings_by_param = []
	for vps in variable_param_strings:
		# If the variable is defined at the top of the cpf, we have already determined it's value
		if vps in known_groundings.keys():
			groundings_by_param.append([known_groundings[vps]])
		# Otherwise, it can be any object of the correct type
		else:
			param_type = pvar_to_param_types[pvar_name]
			groundings_by_param.append(all_object_names[param_type])
	return groundings_by_param
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
def get_goal_conditions_from_reward(reward, conditions_in_reward, solver):
	"""
	:param reward: z3 function var corresponding to the rddl reward.
	:param conditions_in_reward: list of z3 conditions mentioned in reward, in order
	:param solver: z3 Solver with reward function and constants asserted
	:return:
	"""
	goal_conditions = []
	for c_id in range(len(conditions_in_reward)):
		#Check if c True makes reward higher, c False makes reward higher, or unknown. We assume the condition matters, otherwise its poorly defined
		reward_args_true_c = [conditions_in_reward[i] if i != c_id else True for i in range(len(conditions_in_reward))]
		reward_args_false_c = [conditions_in_reward[i] if i != c_id else False for i in range(len(conditions_in_reward))]
		#These conditions are, respectively, c always being good for reward, c always being bad for reward
		c_is_goal = (reward(*reward_args_true_c) >= reward(*conditions_in_reward))
		not_c_is_goal = (reward(*reward_args_false_c) >= reward(*conditions_in_reward))
		# print("assertions for {}: {}".format(c_id,solver.assertions))
		if solver_implies_condition(solver, c_is_goal):
			goal_conditions.append(conditions_in_reward[c_id])
		elif solver_implies_condition(solver,not_c_is_goal):
			goal_conditions.append(z3.Not(conditions_in_reward[c_id]))
	return goal_conditions

def get_reward_conditions(rddl_model, solver=None):
	"""
	:param rddl_model:
	:param solver: solver with constant values asserted
	:return: list of conditions mentioned in z3 reward function, list of pvars mentioned in the reward function outside of conditions, z3 func representing reward function
	"""
	reward_expr = rddl_model.domain.reward
	if(reward_expr.etype[0] == 'control'):
		condition = reward_expr.args[0]
		compiled_reward = _compile_expression(condition,dict(),solver)
		# compiled_reward = AndList()
		return AndList(compiled_reward)
	else:
		#Assume the reward is a sum of sums, or at least has no ifs
		conditions_list = []
		out_of_condition_pvars = []
		grounding_dict = dict()
		compiled_reward = _compile_expression(reward_expr,grounding_dict,solver,conditions_list=conditions_list,out_of_condition_pvars=out_of_condition_pvars)
		# print("Conditions in reward:")
		# for c in conditions_list: print(c)
		#We need to separate pvars that occur only in conditions from pvars that occur outside of conditions.
		#We can do this by passing in an unconditions_pvars list to _compile_expression
		print("reward got")


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
				if (false_case.etype[0] != 'control'):
					for action in actions_list:
						if action in condition.scope:
							#TODO get rid of code duplication between this and next block of code
							#Ground the action based on groundings_from_top.
							cleaned_action_name = action.split("/")[0]
							action_variable_args = get_pvar_args_strings(cleaned_action_name, condition)
							grounded_action_str = plugin_objects_to_pvar(cleaned_action_name,action_variable_args,groundings_from_top)
							condition_grounding_pair = (condition,groundings_from_top)
							#Add to the dictionary.
							action_to_effect_to_precond[grounded_action_str][grounded_state_variable].append(condition_grounding_pair)
				else:
					while (false_case.etype[0] == 'control'):
						for action in actions_list:
							if action in condition.scope:
								# Ground the action based on groundings_from_top.
								cleaned_action_name = action.split("/")[0]
								print(cleaned_action_name)
								if cleaned_action_name == "move_west":
									print("ruroh")
									asdfsadfsa = 8
									print(asdfsadfsa)
								action_variable_args = get_pvar_args_strings(cleaned_action_name, condition)
								grounded_action_str = plugin_objects_to_pvar(cleaned_action_name, action_variable_args,
																			 groundings_from_top)
								condition_grounding_pair = (condition, groundings_from_top)
								# Add to the dictionary.
								action_to_effect_to_precond[grounded_action_str][grounded_state_variable].append(
									condition_grounding_pair)

						condition = false_case.args[0]
						false_case = false_case.args[2]

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

	# Makes a list of the non-fluents (constants) from the domain
	att_name_to_domain_attribute = {}
	rddl2z3_sorts = {
		"bool":z3.Bool,
		"int":z3.Int,
		"real":z3.Real
	}
	#TODO add default values for pvars
	constants = []
	for nonf in model_nonfluents:
		print(nonf)
		rddl_range = model_nonfluents[nonf].range
		z3_sort = rddl2z3_sorts[rddl_range]
		constants.append(DomainAttribute(model_nonfluents[nonf].name, z3_sort, model_nonfluents[nonf].param_types))
	# Makes a list of all the attributes (state variables like passenger-in-taxi)
	attributes_list = []
	for state in model_states:
		rddl_range = model_states[state].range
		z3_sort = rddl2z3_sorts[rddl_range]
		attributes_list.append(DomainAttribute(model_states[state].name, z3_sort, model_states[state].param_types))
			# att_name_to_domain_attribute[model_states[state].name] = model_states[state].args_names

	# Converts the attributes to z3 and assigns them to a dict
	att_name_to_arg_names = {}
	name_to_z3_var = {}
	attribute_to_grounded_names = {}
	for att in attributes_list + constants:
		att_name_to_domain_attribute[att.name] = att
		if att.arguments is None or len(att.arguments) == 0:
			grounded_attributes = [g2n_names(att.name,[])]
		else:
			grounded_attributes = att.ground(all_object_names)
		attribute_to_grounded_names[att.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			# Apply constraints
			pass

	print("grounded atts:")
	for n in name_to_z3_var.keys():
		print(n)
	print("grounded atts over")

	ground2name = instance_building_utils.g2n_names
	ground2var = instance_building_utils.g2v_builder(name_to_z3_var,ground2name)
	# Initialize a z3 solver to be returned when it contains the necessary z3 instantiation of z3 instances
	init_nonfluents = pull_init_nonfluent(rddl_model)
	init_state = pull_init_state(rddl_model)
	# A solver that contains all information about the start state
	solver = z3.Solver()
	#A solver that contains only constant assertions
	solver_constants_only = z3.Solver()

	# Give the passenger, etc. their init values and push them into the solver
	for init_val in init_state:
		solver.add(ground2var(init_val[0][0], init_val[0][1]) == init_val[1])
	# Give all the initial non-fluents their values and push them into the solver
	for init_nonf in init_nonfluents:
		att_name = init_nonf[0][0]
		obj_names = init_nonf[0][1]
		if obj_names is None:
			obj_names = []
		solver.add(ground2var(att_name, obj_names) == init_nonf[1])
		solver_constants_only.add(ground2var(att_name, obj_names) == init_nonf[1])
	# reward_ast = get_reward_conditions(rddl_model, solver_constants_only)
	compiled_reward = get_reward_conditions(rddl_model, solver_constants_only)
	triplet_dict = make_triplet_dict(rddl_model, all_object_names)

	skills_triplets = []
	for action in triplet_dict.keys():
		for effect in triplet_dict[action]:
			for precond in triplet_dict[action][effect]:
				print(precond)
				z3_expr = _compile_expression(*precond,solver_constants_only)
				new_skill = Skill(z3_expr, action, [effect])
				skills_triplets.append(new_skill)
				print("Temp break here!")
	return skills_triplets, compiled_reward, solver
def _compile_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None, in_condition = False):
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
		#'control': _compile_control_flow_expression,
		'aggregation': _compile_aggregation_expression
	}

	etype = expr.etype
	compiler_type = etype[0]
	if compiler_type not in etype2compiler.keys():
		raise ValueError('Expression type unknown: {}'.format(etype))

	#If the compiler_type is one of the following, then the result will be a condition, so we set in_condition=True
	# Some pvars or constants are also conditions, but in those cases there will be no sub-conditions, so we don't need to set in_condition
	condition_compiler_types = ['boolean', 'relational', 'aggregation']
	if compiler_type in condition_compiler_types:
		#TODO avoid making in_condition_new. It's ugly and (probably) avoidable.
		# The most obvious way to avoid it is to handle condition adding in the other _compile_expression functions, but
		#that doesn't seem worth the extra code
		in_condition_new = True
	else:
		in_condition_new = in_condition
	compiler_fn = etype2compiler[compiler_type]
	new_expr =  compiler_fn(expr,groundings_from_top,solver_constants_only,conditions_list,out_of_condition_pvars,in_condition_new)
	#If we are gathering conditions and we are not yet in a condition
	if conditions_list is not None and not in_condition:
		#If the new expression is a condition, add it to the list
		if isinstance(new_expr,z3.z3.BoolRef):
				conditions_list.append(new_expr)
	in_condition = in_condition_new
	return new_expr


def _compile_constant_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only , conditions_list = None, out_of_condition_pvars = None,in_condition = False):
	return expr.value

def _compile_arithmetic_expression(expr: Expression, grounding_dict:Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
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
            x = _compile_expression(args[0], grounding_dict, conditions_list, in_condition)
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
            x = _compile_expression(args[0], grounding_dict,solver_constants_only, conditions_list,out_of_condition_pvars, in_condition)
            y = _compile_expression(args[1], grounding_dict,solver_constants_only, conditions_list,out_of_condition_pvars, in_condition)
            fluent = op(x, y)

        return fluent

def _compile_pvariable_expression(expr: Expression, grounding_dict: Dict[str, str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
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
		object_names = [grounding_dict[x] for x in variable_param_strings]
		z3_var = name_to_z3_var[instance_building_utils.g2n_names(pvar_name,object_names)]
		if out_of_condition_pvars is not None and not in_condition:
			out_of_condition_pvars.append(z3_var)
		return z3_var

def _compile_boolean_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
	#TODO handle [(var,grounding_dict)] list that will be returned from compile_pvariable
	etype = expr.etype
	args = expr.args

	if len(args) == 1:
		etype2op = {
			'~': lambda x: z3.Not(x)
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid unary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0], groundings_from_top,solver_constants_only, conditions_list, in_condition)
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
			'|': lambda x, y: or2(x, y, solver=solver_constants_only),
			'=>': lambda x, y: or2(z3.Not(x), y),
			'<=>': lambda x, y: or2(z3.And(*[x, y]), z3.And(*[z3.Not(x), z3.Not(y)]))
		}

		if etype[1] not in etype2op:
			raise ValueError('Invalid binary boolean expression:\n{}'.format(expr))

		op = etype2op[etype[1]]
		x = _compile_expression(args[0],groundings_from_top,solver_constants_only, conditions_list, out_of_condition_pvars,in_condition)
		y = _compile_expression(args[1],groundings_from_top,solver_constants_only, conditions_list, out_of_condition_pvars,in_condition)
		bool_in_z3 = op(x, y)

	return bool_in_z3


# Done!
def _compile_relational_expression(expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
	#TODO handle [(var,grounding_dict)] list that will be returned from compile_pvariable

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
	x = _compile_expression(args[0],groundings_from_top,solver_constants_only, conditions_list, out_of_condition_pvars,in_condition)
	y = _compile_expression(args[1],groundings_from_top,solver_constants_only, conditions_list, out_of_condition_pvars,in_condition)
	fluent = op(x, y)

	return fluent

def _compile_random_variable_expression(self,
                                            expr: Expression, groundings_from_top: Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
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

def _compile_aggregation_expression(expr: Expression, grounding_dict: Dict[str,str],solver_constants_only, conditions_list = None, out_of_condition_pvars = None,in_condition = False):
	#TODO test against aggregators that introduce multiple vars, ex. forall_{?x, ?y}

	# These functions in the values of the dict are incorrect, make sure to make them better. I have no clue
	# how to do this...
	etype2aggr = {
		'sum': lambda x: z3.Sum(x),
		# 'prod': x.prod,
		# 'avg': x.avg,
		# 'maximum': x.maximum,
		# 'minimum': x.minimum,
		'exists': lambda x: or2(*x),
		'forall': lambda x: AndList(*x)
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
		compiled_expressions.append(_compile_expression(expr2compile, new_grounding_dict,solver_constants_only,conditions_list,out_of_condition_pvars,in_condition))
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
	#	test_dict = make_triplet_dict(model)
		model_states = pull_state_var_dict(model)
		model_non_fluents = pull_nonfluent_var_dict(model)
		instance_objects = pull_instance_objects(model)
		instance_nonfluents = pull_init_nonfluent(model)
		initial_state = pull_init_state(model)
		# reward_condition = get_reward_conditions(model)

		skill_triplets, compiled_reward, solver = convert_to_z3(model)
		return compiled_reward, skill_triplets, solver

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

		skill_triplets, compiled_reward, solver = convert_to_z3(rddl_model)
		print("skills:")
		for s in skill_triplets: print(s)