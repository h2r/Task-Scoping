from z3 import *

def tactic1():
	x, y = Reals('x y')
	g  = Goal()
	g.add(x > 0, y > 0, x == y + 2)
	print(g)

	t1 = Tactic('simplify')
	t2 = Tactic('solve-eqs')
	t  = Then(t1, t2)
	print(t(g))
def split_clause_ex():
	x, y = Reals('x y')
	g = Goal()
	g.add(Or(x < 0, x > 0), x == y + 1, y < 0)

	t = Tactic('split-clause')
	r = t(g)
	for g in r:
		print(g)

def var2str():
	names = list(range(3))
	vars = [z3.Bool(n) for n in names]
	a = And(*vars[:2])
	print(a)
def is_condition():
	bool0 = z3.Bool('bool0')
	int0 = z3.Int("int0")
	int1 = z3.Int("int1")
	print(bool0.__class__)
	equality0 = (int0==int1)
	print(equality0.__class__)
def ast_v_var_example():
	b0 = z3.Bool('b0')
	b1 = z3.Bool('b1')
	b0_or_b1 = z3.Or(b0,b1)
	assert b0.num_args() == 0
	assert b0_or_b1.num_args() == 2
def boolref_check():
	x = z3.Bool('x')
	assert isinstance(x,z3.BoolRef)

def adding_bools_example():
	b0 = z3.Bool('b0')
	b1 = z3.Bool('b1')
	x1 = z3.If(b0,1,0)
	x2 = z3.If(b1,1,0)
	x1_x2 = z3.Sum(x1,x2)
	print(x1_x2)
	try:
		b0_b1 = z3.Sum(b0,b1)
		crashed = False
	except:
		crashed = True
	if not crashed:
		raise Exception("Should have raised z3 exception for adding bools")

def expr_sorts():
	b0 = z3.Bool('b0')
	print(b0.sort() == z3.BoolSort())
def foo():
	f = Function('f', IntSort(), IntSort(), IntSort())
	x, y = Ints('x y')
	print(ForAll([x, y], f(x, y) == 0))
	print(Exists(x, f(x, x) >= 0))

	print(" ")
	f = Function('f', IntSort(), IntSort(), IntSort())
	x, y = Ints('x y')
	f = ForAll([x, y], f(x, y) == 0)
	print(f.body())
	v1 = f.body().arg(0).arg(0)
	print(v1)
	print(eq(v1, Var(1, IntSort())))

def sets_example():
	is_passenger = Function('is_passenger', Int)
if __name__ == "__main__":
	# split_clause_ex()
	# is_condition()
	# ast_v_var_example()
	# boolref_check()
	# adding_bools_example()
	# expr_sorts()
	foo()