import z3

# z3.z3core.
def and_z3(a,b):
	return z3.And(a,b)

def rddl2z3(ast):
	#deal with quantifiers, functions, constants
	pass