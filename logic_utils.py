import z3
from classes import AndList

def get_var_names(expr):
	if isinstance(expr, bool):
		return []
	vars = [str(i) for i in z3.z3util.get_vars(expr)]
	return vars
def solver_implies_condition(solver, precondition):
	# print("Assertions:")
	# for a in solver.assertions(): print(a)
	solver.push()
	# assert z3.is_expr(precondition), "{}; {}".format(type(precondition),precondition)
	# print(type(precondition))
	solver.add(z3.Not(precondition))
	# print("Assertions (including not precondition):")
	# for a in solver.assertions(): print(a)
	# print("Assertions over")
	result = solver.check()
	solver.pop()
	if result == z3.z3.unsat:
		# print("result: {}".format(result))
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown guarantee for precondition: {}".format(precondition))
		# print("result: {}".format(result))
		return False

def check_implication(antecedent, consequent):
	#TODO make global empty solver instead of creating new one every time. Creating a solver may take nontrivial time
	if isinstance(antecedent,AndList):
		antecedent = antecedent.to_z3()
	if isinstance(consequent,AndList):
		consequent = consequent.to_z3()
	solver = z3.Solver()
	solver.add(antecedent)
	solver.add(z3.Not(consequent))
	result = solver.check()
	if result == z3.z3.unsat:
		return True
	else:
		if result == z3.z3.unknown:
			print("Unknown implication for precondition: {} => {}".format(antecedent,consequent))
		return False