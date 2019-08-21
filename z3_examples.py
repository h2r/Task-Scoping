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

if __name__ == "__main__":
	split_clause_ex()