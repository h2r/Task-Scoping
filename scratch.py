import z3
import timeit
import itertools
def test_solver_construction_time(n=1000):
	t = timeit.Timer(stmt ="s = z3.Solver()", setup="import z3")
	print(t.timeit(n))

def empty_product():
	a = itertools.product()
	for x in a:
		print('car')

# test_solver_construction_time()
empty_product()