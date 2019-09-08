import z3
from logic_utils import solver_implies_condition, get_iff
from pyrddl_inspector import get_goal_conditions_from_reward
# print(result)


def get_goal_conditions_test(num_args = 3):
	bool_vars = [z3.Bool("generic_{}".format(i)) for i in range(num_args)]
	#Test 1: sum of bools
	s = z3.Solver()
	reward_signature = [z3.BoolSort() for _ in range(num_args)] + [z3.IntSort()]
	reward = z3.Function("reward", *reward_signature)
	reward_expr = z3.Sum([z3.If(bool_vars[i],1,0) for i in range(len(bool_vars))])
	reward_definition = z3.ForAll(bool_vars, reward(*bool_vars) == reward_expr)
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

def define_reward_based_on_condition_test():
	x = z3.Int('x')
	y = z3.Int('y')
	x_eq_y = (x == y)
	print(isinstance(x_eq_y,z3.z3.BoolRef))
	f = z3.Function('f',z3.BoolSort(),z3.IntSort())
	s = z3.Solver()
	f_def = z3.ForAll([x_eq_y], f(x_eq_y) == z3.If(x_eq_y,1,0))
	s.add(f_def)
	goal_conditions = get_goal_conditions_from_reward(f,[x_eq_y],s)
	print(goal_conditions)

def synthetic_constants_test():
	s = z3.Solver()
	x = z3.Int('x')
	y = z3.Int('y')
	x_eq_y_expr = (x == y)
	x_eq_y_const = z3.Bool('x_eq_y_const')
	x_eq_y_binding = get_iff(x_eq_y_const,x_eq_y_expr)
	s.add(x_eq_y_binding)
	#Test that the binding works
	s.push()
	s.add(x_eq_y_expr == True)
	s.add(x_eq_y_const == False)
	assert s.check() == z3.z3.unsat
	s.pop()
	s.push()
	s.add(x_eq_y_expr)
	# s.add(x != y)
	s.add(x==3)
	s.add(y==4)
	assert s.check() == z3.z3.unsat
	s.pop()
	s.add(x_eq_y_const)
	s.add(x == 3)
	s.add(y==4)
	assert s.check() == z3.z3.unsat
	#
	# assert s.check == z3.z3.unsat

	# print(isinstance(x_eq_y_expr,z3.z3.BoolRef))
	f = z3.Function('f',z3.BoolSort(),z3.IntSort())
	f_def = z3.ForAll([x_eq_y_const], f(x_eq_y_const) == z3.If(x_eq_y_const,1,0))
	s.add(f_def)
	goal_conditions = get_goal_conditions_from_reward(f,[x_eq_y_const],s)
	print(goal_conditions)

def get_iff_test():
	b0 = z3.Bool('b0')
	b1 = z3.Bool('b1')
	b0_iff_b1 = get_iff(b0,b1)

def eq_test():
	x = z3.Int('x')
	y = z3.Int('y')
	assert z3.eq(x+y,x+y) == True
	assert z3.eq(x+y,y+x) == False
if __name__ == "__main__":
	# get_goal_conditions_test()
	synthetic_constants_test()
	# get_iff_test()
	# eq_test()