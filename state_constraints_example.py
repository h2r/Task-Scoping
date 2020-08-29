import re, copy, itertools, z3, time, sys, pprint
from action import Action
from PDDLz3 import PDDL_Parser_z3, compile_expression, str2expression, extract_typed_objects
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms, get_all_objects, condition_str2objects
from scoping import scope
pp = pprint.PrettyPrinter(indent=4)

constraint_s = """(
	forall (?t - taxi ?p0, ?p1 - passenger) 
	(not
		(and
			(
    			(in-taxi ?p0 ?t) (in-taxi ?p1 ?t) (not (= ?p0 ?p1))
    		)
    	)
    )
)"""

def parse_tokens2(my_str):
    stack = []
    l2 = []
    for t in re.findall(r'[()]|[^\s()]+', my_str):
        if t == '(':
            stack.append(l2)
            l2 = []
        elif t == ')':
            if stack:
                l = l2
                l2 = stack.pop()
                l2.append(l)
            else:
                raise Exception('Missing open parentheses')
        else:
            l2.append(t)
    if stack:
        raise Exception('Missing close parentheses')
    if len(l2) != 1:
        raise Exception('Malformed expression')
    return l2[0]
def split_predicates2(group):
    pos = []
    neg = []
    if not type(group) is list:
        raise Exception('Error with ')
    if group == []:
        # pass
        return
        # from IPython import embed; embed()
    if group[0] == 'and':
        group.pop(0)
    else:
        group = [group]
    for predicate in group:
        if predicate[0] == 'not':
            if len(predicate) != 2:
                raise Exception('Unexpected not in ')
            neg.append(predicate[-1])
        else:
            pos.append(predicate)
    return pos, neg

tokens = parse_tokens2(constraint_s)
pp.pprint(tokens)
pos, neg = split_predicates2(tokens)
pp.pprint(pos)

domain, problem = "examples/taxi-state-constraint/taxi-domain.pddl", "examples/taxi-state-constraint/prob-02.pddl"

parser = PDDL_Parser_z3()
parser.parse_domain(domain)
parser.parse_problem(problem)

# constraint_expr = compile_expression(pos[0], parser.make_str2var_dict(), parser)
constraint_expr = str2expression(constraint_s, parser)
print(constraint_expr)