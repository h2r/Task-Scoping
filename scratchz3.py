import z3
from utils import expr2pvar_names_single, get_atoms
tactic_names = ['ackermannize_bv', 'subpaving', 'horn', 'horn-simplify', 'nlsat', 'qfnra-nlsat', 'nlqsat', 'qe-light',
				'qe-sat', 'qe', 'qsat', 'qe2', 'qe_rec', 'psat', 'sat', 'sat-preprocess', 'ctx-solver-simplify', 'smt',
				'psmt', 'unit-subsume-simplify', 'aig', 'add-bounds', 'card2bv', 'degree-shift', 'diff-neq', 'eq2bv',
				'factor', 'fix-dl-var', 'fm', 'lia2card', 'lia2pb', 'nla2bv', 'normalize-bounds', 'pb2bv',
				'propagate-ineqs', 'purify-arith', 'recover-01', 'bit-blast', 'bv1-blast', 'bv_bound_chk',
				'propagate-bv-bounds', 'propagate-bv-bounds-new', 'reduce-bv-size', 'bvarray2uf', 'dt2bv',
				'elim-small-bv', 'max-bv-sharing', 'blast-term-ite', 'cofactor-term-ite', 'collect-statistics',
				'ctx-simplify', 'der', 'distribute-forall', 'dom-simplify', 'elim-term-ite', 'elim-uncnstr',
				'injectivity', 'snf', 'nnf', 'occf', 'pb-preprocess', 'propagate-values', 'reduce-args',
				'reduce-invertible', 'simplify', 'elim-and', 'solve-eqs', 'special-relations', 'split-clause',
				'symmetry-reduce', 'tseitin-cnf', 'tseitin-cnf-core', 'qffd', 'pqffd', 'smtfd', 'fpa2bv', 'qffp',
				'qffpbv', 'qffplra', 'default', 'sine-filter', 'qfbv-sls', 'nra', 'qfaufbv', 'qfauflia', 'qfbv',
				'qfidl', 'qflia', 'qflra', 'qfnia', 'qfnra', 'qfuf', 'qfufbv', 'qfufbv_ackr', 'ufnia', 'uflra',
				'auflia', 'auflira', 'aufnira', 'lra', 'lia', 'lira', 'skip', 'fail', 'fail-if-undecided',
				'macro-finder', 'quasi-macros', 'ufbv-rewriter', 'bv', 'ufbv']



def simplify_test():
	"""We want to simplify Or(And(A,B),And(A,Not(B))) to A"""
	A = z3.Bool('A')
	B = z3.Bool('B')
	both = z3.And(A,B)
	Aonly = z3.And(A,z3.Not(B))
	Acomp = z3.Or(both,Aonly)

	print(Acomp)
	g = z3.Goal()
	g.add(Acomp)
	print(g)
	boring_output = '[[Or(And(A, B), And(A, Not(B)))]]'
	boring_tactics = []
	interesting_tactics = []
	exceptions = {}
	for tn in tactic_names:
		t = z3.Tactic(tn)
		try:
			s = str(t(g))
		except Exception as e:
			exceptions[tn] = e
		if s == boring_output:
			boring_tactics.append(tn)
		else:
			print(f"{tn}:\n{s}\n")
			interesting_tactics.append(tn)
	print(f"Boring tactics:\n{', '.join(boring_tactics)}")
	print(f"\nInteresting tactics:\n{', '.join(interesting_tactics)}")
	print(f"\nExceptions: ")
	for k,v in exceptions.items():
		print(f"{k}: {v}")

	successful_tactics = ['ctx-solver-simplify', 'aig']

def split_conjunction():
	A = z3.Bool('A')
	B = z3.Bool('B')
	both = z3.And(A,B)
	Aonly = z3.And(A,z3.Not(B))
	Acomp = z3.Or(both,Aonly)
	print(str(both))
	g = z3.Goal()
	g.add(both)
	print(str(g))
	print(g.as_expr())

	boring_output = '[[A, B]]'
	boring_tactics = []
	interesting_tactics = []
	exceptions = {}
	for tn in tactic_names:
		t = z3.Tactic(tn)
		try:
			s = str(t(g))
		except Exception as e:
			exceptions[tn] = e
		if s == boring_output:
			boring_tactics.append(tn)
		else:
			print(f"{tn}:\n{s}\n")
			interesting_tactics.append(tn)
	print(f"Boring tactics:\n{', '.join(boring_tactics)}")
	print(f"\nInteresting tactics:\n{', '.join(interesting_tactics)}")
	print(f"\nExceptions: ")
	for k, v in exceptions.items():
		print(f"{k}: {v}")

def split_into_conjunctions():
	atoms = [z3.Bool(str(i)) for i in range(4)]
	first2 = z3.And(*atoms[:2])
	last2 = z3.And(*atoms[2:])
	first2OrLast2 = z3.Or(first2, last2)
	g = z3.Goal()
	g.add(first2OrLast2)
	r = z3.Tactic('split-clause')(g)
	print(first2OrLast2)
	print(r[0].as_expr())
	for x in r:
		print(x.as_expr())


if __name__ == "__main__":
	# split_conjunction()
	split_into_conjunctions()