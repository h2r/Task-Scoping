import z3
from logic_utils import solver_implies_condition
# num_bools = 5
# generic_bools = [z3.Bool("generic_{}".format(i)) for i in range(num_bools)]
# x,y,z = generic_bools[:3]
# sum_of_bools = z3.Sum([z3.If(generic_bools[i],1,0) for i in range(num_bools)])
# #A solver can only have a single value for each variable. I think I need to make an explicit function
# reward_signature = [z3.BoolSort() for _ in range(2)] + [z3.IntSort()]
# reward = z3.Function("reward",*reward_signature)
# reward_one_arg = z3.Function("reward",z3.BoolSort(),z3.IntSort())
# s = z3.Solver()
# s.add(z3.ForAll(generic_bools[:2], reward(*generic_bools[:2]) == z3.Sum([z3.If(generic_bools[i],1,0) for i in range(2)])))
# s.add(generic_bools[0] == True)
# # s.add(generic_bools[1] == True)
# result = s.check(reward(True,True) != 2)
# print(result)
def get_goal_conditions_from_reward(reward, conditions_in_reward, solver):
	"""
	:param reward: z3 function
	:param conditions_in_reward: list of z3 conditions mentioned in reward, in order
	:param solver: z3 Solver with reward function and constants defined
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

		if solver_implies_condition(solver, c_is_goal):
			goal_conditions.append(conditions_in_reward[c_id])
		elif solver_implies_condition(solver,not_c_is_goal):
			goal_conditions.append(z3.Not(conditions_in_reward[c_id]))
	return goal_conditions


def get_goal_conditions_example(num_args = 3):
	s = z3.Solver()
	bool_vars = [z3.Bool("generic_{}".format(i)) for i in range(num_args)]

	reward_signature = [z3.BoolSort() for _ in range(num_args)] + [z3.IntSort()]
	reward = z3.Function("reward", *reward_signature)
	s.add(z3.ForAll(bool_vars, reward(*bool_vars) == z3.Sum([z3.If(bool_vars[i],1,0) for i in range(len(bool_vars))])))
	# x = solver_implies_condition(s,reward(True,True,bool_vars[2]) >= reward())
	# print(x)
	goal_conditions = get_goal_conditions_from_reward(reward,bool_vars,s)
	print(goal_conditions)
	assert goal_conditions == bool_vars

	goal_conditions = []

if __name__ == "__main__":
	get_goal_conditions_example()