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
if __name__ == "__main__":
	# split_clause_ex()
	# is_condition()
	# ast_v_var_example()
	boolref_check()