import z3
from logic_utils import solver_implies_condition
from pyrddl_inspector import get_goal_conditions_from_reward
# print(result)


def get_goal_conditions_test(num_args = 3):
	bool_vars = [z3.Bool("generic_{}".format(i)) for i in range(num_args)]
	#Test 1: sum of bools
	s = z3.Solver()
	reward_signature = [z3.BoolSort() for _ in range(num_args)] + [z3.IntSort()]
	reward = z3.Function("reward", *reward_signature)
	reward_definition = z3.ForAll(bool_vars, reward(*bool_vars) == z3.Sum([z3.If(bool_vars[i],1,0) for i in range(len(bool_vars))]))
	s.add(reward_definition)
	# x = solver_implies_condition(s,reward(True,True,bool_vars[2]) >= reward())
	# print(x)
	goal_conditions = get_goal_conditions_from_reward(reward,bool_vars,s)
	print(goal_conditions)
	assert goal_conditions == bool_vars

	#Test 2: exclusive or
	s = z3.Solver()
	reward2 = z3.Function('reward2',*reward_signature)
	#NOTE: z3.Xor accepts only two args. Also, apparently xor is hard for dppl-like solvers
	reward2_definition = z3.ForAll(bool_vars,reward2(*bool_vars) == z3.If(z3.Xor(bool_vars[0],z3.Xor(bool_vars[1],bool_vars[2])),1,0))
	s.add(reward2_definition)
	goal_conditions_true = []
	goal_conditions_empirical = get_goal_conditions_from_reward(reward2,bool_vars,s)
	print(goal_conditions_empirical)
	assert goal_conditions_empirical == goal_conditions_true



	goal_conditions = []

if __name__ == "__main__":
	get_goal_conditions_test()