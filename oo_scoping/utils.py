import re, os, copy
from abc import ABC
from collections.abc import Iterable
from typing import Union, List
from itertools import product, chain
import pathlib
import pdb
import z3

# TODO Split this into multiple scripts. Remove unneeded functions.

solver = z3.Solver()
synth2varnames = {}

def get_scoped_problem_path(p, suffix = None):
    p_split = p.split(".")
    base = ".".join(p_split[:-1])
    if suffix is None:
        suffix = ""
    else:
        suffix = "_" + suffix
    return base + "_scoped" + suffix + "." +  p_split[-1]

def get_scoped_domain_path(d, p, suffix = None):
    d_split = d.split(".")
    base = ".".join(d_split[:-1])
    # p_id = re.search("([0-9]+)",p).group()
    p_name = p.split("/")[-1]
    p_base = ".".join(p_name.split(".")[:-1])

    if suffix is None:
        suffix = ""
    else:
        suffix = "_" + suffix
    d_new = base + "_" + "scoped" + "_"  + p_base + suffix + "." + d_split[-1]
    return d_new

def find_closing_paren(s, start):
    lefts_left = 0
    for i in range(start, len(s)):
        c = s[i]
        if c == ")":
            lefts_left -= 1
            if lefts_left == 0:
                return i
        elif c == "(":
            lefts_left += 1

def pvars2objects(pvars):
        objs = condition_str2objects(map(str,pvars))
        objs = [s.strip() for s in objs]
        objs = sorted(list(set(objs)))
        return objs

def writeback_domain(input_path, output_path, actions):
    with open(input_path, "r") as f:
        domain = f.read()
    # TODO find any of a list of action names
    for action in actions:
        action_prefix = "\(:action " + action
        action_start = re.search(action_prefix, domain).start()
        action_end = find_closing_paren(domain, action_start) + 1
        action_lines = domain[action_start:action_end].splitlines()
        action_lines = [";" + l for l in action_lines]
        action_commented = "\n".join(action_lines)
        domain = domain[:action_start] + action_commented + domain[action_end:]
    with open(output_path, "w") as f:
        f.write(domain)

# TODO clean this up, maybe make less janky
def writeback_problem(input_path, output_path, objects):
    with open(input_path, "r") as f:
        instance_lines = f.read().splitlines()
    scoped_lines = []
    in_objects_flag = False
    for l in instance_lines:
        if in_objects_flag == True:
            l_stripped = l.replace("\t","").replace(" ","")
            if len(l_stripped) > 0 and l_stripped[0] == ")":
                in_objects_flag = False
        elif "(:objects" in l:
            in_objects_flag = True
        
        tokens = re.split('[ (),]',l)
        tokens[0] = tokens[0].strip('\t')
        
        if not any(o in tokens for o in objects):
            scoped_lines.append(l)
        
        else:
            # from IPython import embed; embed()
            if in_objects_flag:
                split_l = l.split(" ")
                obj_type = split_l[-1]
                objs = [o.replace("\t","") for o in split_l[:-2]]
                objs_kept = []
                objs_removed = []
                # objs = [o for o in objs if o not in objects and o != '']
                for o in objs:
                    if o in objects:
                        objs_removed.append(o)
                    else:
                        objs_kept.append(o)
                objs_kept = [i for i in objs_kept if i]
                if len(objs_kept) > 0:
                    l_new = "\t" + " ".join(objs_kept) + " - " + obj_type
                    scoped_lines.append(l_new)
                if len(objs_removed) > 0:
                    l_new = ";\t" + " ".join(objs_removed) + " - " + obj_type
                    scoped_lines.append(l_new)
            else:
                # print(l)
                scoped_lines.append(";" + l)

    with open(output_path, "w")  as f:
        f.write("\n".join(scoped_lines))

# def get_var_names(expr):
# 	vars = [str(i) for i in z3.z3util.get_vars(expr)]
# 	return vars
def simplify_disjunction(conds, my_solver=None, tactic='aig'):
    #tactic = 'simplify'
    global solver
    if my_solver is None: my_solver = solver
    if not isinstance(conds, Iterable):
        conds = [conds]
    disj = z3.Or(*conds)
    g = z3.Goal()
    g.add(disj)
    disj_simp = z3.Tactic(tactic)(g).as_expr()
    if disj_simp.decl().name() == 'and':
        disj_simp = z3.And(*disj_simp.children())
    return disj_simp

def split_conj(expr):
    if isinstance(expr, bool):
        return expr
    elif z3.is_expr(expr):
        if expr.decl().name() == 'and':
            return expr.children()
        else:
            return [expr]
    else:
        raise TypeError(f"Can't split type {type(expr)}")
#
#
#
# def test_grounded_att2objects(silent=False):
# 	att_name = "att"
# 	object_names = ["x0", "x1"]
# 	for i in range(len(object_names) + 1):
# 		object_names_true = object_names[:i]
# 		att_str = g2n_names(att_name,object_names_true[:i])
# 		# print("Input str:\n{}".format(att_str))
# 		object_names_emp = grounded_att2objects(att_str)
# 		assert object_names_true == object_names_emp, str(object_names_emp)
# 	if not silent: print("")
def condition_str2objects(prop_str_list):
    if isinstance(prop_str_list, str):
        prop_str_list = [prop_str_list]
    objects = []
    for prop_str in prop_str_list:
        try:
            paren_groups = re.findall("\(([^()]*)\)",prop_str)
        except TypeError as e:
            print(prop_str)
            print(type(prop_str))
            print(prop_str_list)
            raise e
        for p in paren_groups:
            split_p = p.split(",")
            objects += split_p
    objects = list(set(objects))
    objects.sort()
    return objects
# TODO make condition_str2vars().
def condition_str2objects_test():
    prop_str = "synth_Or(Not(PASSENGERS_YOU_CARE_FOR(p0)),\nAnd(Not(in-taxi(p0,t0)),\npass-x-curr(p0) == PASSENGER_GOAL_X(p0),pass-y-curr(p0) == PASSENGER_GOAL_Y(p0)))"
    objects = condition_str2objects(prop_str)
    print(objects)
def get_all_bitstrings(n: int):
    if n == 1:
        return [[0], [1]]
    else:
        l = get_all_bitstrings(n-1)
        l2 = []
        for x in l:
            l2.append(x + [0])
            l2.append(x + [1])
        return l2


def expr2pvar_names_single(expr):  #Do we still have synthvars?
    global synth2varnames
    if isinstance(expr, bool):
        return []
    my_vars = []
    # try:
    #     variter = z3.z3util.get_vars(expr)
    # except Exception as e:
    #     print(expr)
    #     raise e
    for i in z3.z3util.get_vars(expr):
        i = str(i)
        if i in synth2varnames.keys():
            my_vars = my_vars + synth2varnames[i]
        else:
            my_vars.append(i)
    return sorted(list(set(my_vars)))


def expr2pvar_names(expressions):
    """Gets var names for a list of expressions"""
    if not isinstance(expressions, Iterable):
        expressions = [expressions]
    pvars = []
    for e in expressions:
        pvars.extend(expr2pvar_names_single(e))
    pvars = sorted(list(set(pvars)))
    return pvars

def get_all_objects(skills):
    all_pvars = []
    for s in skills:
        all_pvars.extend(expr2pvar_names_single(s.precondition))
        # Add params, if they exist
        if hasattr(s, "params"):
            all_pvars.extend(s.params)
    all_objects = []
    for x in all_pvars:
        all_objects.extend(condition_str2objects(x))

    all_objects = sorted(list(set(all_objects)))
    return all_objects



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
            raise TimeoutError("solver returned unknown")
        # print("result: {}".format(result))
        return False


def check_implication(antecedent, consequent):
    global solver
    # We need to push and pop!
    solver.push()
    solver.add(antecedent)
    solver.add(z3.Not(consequent))
    result = solver.check()
    solver.pop()
    if result == z3.z3.unsat:
        return True
    else:
        if result == z3.z3.unknown:
            print("Unknown implication for precondition: {} => {}".format(antecedent, consequent))
        return False


def provably_contradicting(*args, my_solver=None):
    # Returns True if we can prove a and b are contradictory. False otherwise.
    # Pass in a solver if you want to use background information to check the contradiction.
    # You should probably only pass in a solver that contains propositions about constants
    # We use the name my_solver instead of solver to avoid mucking with the global var.
    global solver
    if my_solver is None: my_solver = solver
    my_solver.push()
    for x in args:
        my_solver.add(x)
    result = my_solver.check()
    my_solver.pop()
    # If it is sat, or unknown, return False
    return result == z3.z3.unsat

def get_possible_values(expr_list, obj, solver = None):
    # https://stackoverflow.com/questions/13395391/z3-finding-all-satisfying-models
    # 			TODO make get_possible_values take list of consts.
    if z3.is_expr(expr_list):
        expr_list = [expr_list]
    if solver is None: solver = z3.Solver()
    solver.push()
    solver.add(*expr_list)
    vals = []
    while solver.check() == z3.sat:
        v = solver.model()[obj]
        vals.append(v)
        solver.add(obj != v)
    return vals

def get_atoms(*args: Union[bool, z3.ExprRef, z3.Goal], remove_constants = True) -> List[z3.ExprRef]:
    #TODO remove duplicates
    atoms = []
    for expr in args:
        if isinstance(expr, (bool, int)): return []
        if isinstance(expr, z3.Goal):
            expr = expr.as_expr()
        children = expr.children()
        # An expression is an atom iff it has no children
        if len(children) == 0:
            atoms.append(expr)
        else:
            # atoms = []
            for c in children:
                atoms.extend(get_atoms(c))
    if remove_constants:
        atoms_filtered = []
        for a in atoms:
            if not isinstance(a, z3.IntNumRef) and str(a) not in ["And", "Or"]:
                atoms_filtered.append(a)
        atoms = atoms_filtered
    return atoms


def get_atoms_test():
    A = z3.Bool('A')
    B = z3.Bool('B')
    both = z3.And(A, B)
    Aonly = z3.And(A, z3.Not(B))
    Acomp = z3.Or(both, Aonly)
    assert set(get_atoms(both)) == {A, B}, set(get_atoms(both))
    assert set(get_atoms(Aonly)) == {A, B}, set(get_atoms(Aonly))

def get_diff_and_int(a,b):
    a_only = [x for x in a if x not in b]
    intersection = [x for x in a if x in b]
    b_only = [x for x in b if x not in intersection]
    return a_only, intersection, b_only
def str_iter(itr):
    return [str(x) for x in itr]

def flatten(arr, exclusions = (str,)):
    new_arr = []
    for x in arr:
        if isinstance(x,Iterable) and not isinstance(x,exclusions):
            new_arr.extend(flatten(x))
        else:
            new_arr.append(x)
    return new_arr


def product_dict(**kwargs):
    keys = kwargs.keys()
    vals = kwargs.values()
    for instance in product(*vals):
        yield dict(zip(keys, instance))
        
def nested_list_replace(arr, replacements):
    if isinstance(arr, str):
        return replacements.get(arr,arr)
    elif isinstance(arr, list):
        arr2 = []
        for x in arr:
            x2 = nested_list_replace(x, replacements)
            arr2.append(x2)
        return arr2
        # return [nested_list_replace(x, replacements) for x in arr]
    else:
        raise TypeError(f"Unsupported type: {type(arr)}")
    
def get_unique_z3_vars(args):
    vars = get_unique_z3_vars_unsorted(args)
    vars = sort_z3_vars(vars)
    return vars

def get_unique_z3_vars_unsorted(args, fast=True):
    """
    :param args: List of z3 vars
    :param fast: When True, check for equality based on string equality only
    """
    if fast:
        args_s = map(str,args)
        idx = []
        uvars_s = []
        for i, s in enumerate(args_s):
            if s not in uvars_s:
                idx.append(i)
                uvars_s.append(s)
        uvars = [args[i] for i in idx]
    else:
        uvars = []
        for x in args:
            if x not in uvars:
                uvars.append(x)
    return uvars

def sort_z3_vars(vars):
    return sorted(vars, key=lambda x: str(x))

def make_dir(*ps, is_file=False):
    """
    :param ps: Iterable of paths
    :param is_file: Whether ps contains file paths or directory paths
    Recursively create p, and parent directories, if they do not yet exist
    """
    for p in ps:
        if is_file:
            p = pathlib.Path(p).parent
        # Get list of ancestor directories
        p_bottom = p
        p_prev = None
        ancestors = []
        while p_prev != p:
            ancestors.append(p)
            p_prev = p
            p = p.parent
        ancestors.reverse()
        # Create ancestor directories, for those that don't exist
        for p_anc in ancestors:
            if not os.path.exists(p_anc):
                os.mkdir(p_anc)

if __name__ == "__main__":
    # test_grounded_att2objects("grounded_att2objects passed tests")
    # condition_str2objects_test()
    print(get_all_bitstrings(3))

