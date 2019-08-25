import z3
import timeit
def test_solver_construction_time(n=1000):
	t = timeit.Timer(stmt ="s = z3.Solver()", setup="import z3")
	print(t.timeit(n))

test_solver_construction_time()