import z3
def get_var_names(x):
	vars = [str(i) for i in z3.z3util.get_vars(x)]
	return vars