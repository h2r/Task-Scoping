from action import Action
from PDDL import PDDL_Parser
import sys, pprint
from collections import OrderedDict
from typing import List, Tuple, Dict, Iterable
import re, copy
import itertools
import z3
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms
from scoping import scope

str2operator = {
    "<": lambda a, b: a < b,
    "<=": lambda a, b: a <= b,
    ">": lambda a, b: a > b,
    ">=": lambda a, b: a >= b,
    "=": lambda a, b: a == b,
    "*": lambda a, b: a * b,
    "+": lambda a, b: a + b,
    "/": lambda a, b: a / b,
    "-": lambda a, b: a - b,
    "increase": lambda a, b: a + b,
    "decrease": lambda a, b: a - b,
    "assign": lambda a, b: b
    }

def list2var_str(x):
    return x[0] + "(" + ", ".join(x[1:]) + ")"

def list_is_flat(l):
    for x in l: 
        if isinstance(x, list):
            return False
    return True

def action2precondition(a: Action, str_var_dict) -> z3.BoolRef:
    clauses = [compile_expression(p, str_var_dict) for p in a.positive_preconditions] + [z3.Not(compile_expression(p, str_var_dict)) for p in a.negative_preconditions]
    return z3.And(*clauses)

def z3_identical(a, b):
    return a.sort() == b.sort() and str(a) == str(b)

def make_z3_atoms(things_dict, z3_class, str2var = None):
    """
    things_dict should be parser.predicates or parser.functions
    z3_class should be z3.Bool or z3.Int
    str2var is the dictionary you want to update. If none, a new OrderedDict is created
    """
    if str2var is None:
        str2var = OrderedDict()
    for p_name, p_args in things_dict.items():
        groundings = product_dict(**OrderedDict([(varnm, parser.get_objects_of_type(vartype)) for (varnm, vartype) in p_args.items()]))
        for x in groundings:
            s = p_name + "(" + ", ".join(x.values()) + ")"
            grounded_predicate = z3_class(s)
            assert s not in str2var.keys(), f"{s}: {str2var[s]}, {grounded_predicate}"
            str2var[s] = grounded_predicate
    return str2var

def compile_expression(expr, str_var_dict):
    """ 
    :param expr - a (potentially nested) list of strings
    :param str_var_dict - a dictionary mapping strings representing pvars to their corresponding z3 objects
    """
    if isinstance(expr, int):
        return expr
    elif isinstance(expr, str):
        try:
            expr = int(expr)
            return expr
        except ValueError as e:
            from IPython import embed; embed()
            raise e
    elif isinstance(expr, list):
        if list_is_flat(expr):
            return str_var_dict[list2var_str(expr)]
        elif len(expr) == 2:
            if expr[0] == "not":
                return z3.Not(compile_expression(expr[1], str_var_dict))
        else:
            assert len(expr) == 3, f"Don't understand how to compile: {expr}"
            operator = str2operator[expr[0]]
            operator_args = [compile_expression(x, str_var_dict) for x in expr[1:]]
            return operator(*operator_args)
    else:
        raise NotImplementedError(f"Don't understand how to compile non lists: {expr}; {type(expr)}")

def action2effect_types(a: Action, str_var_dict) -> List[EffectTypePDDL]:
    effect_types = []

    for eff in a.add_effects:
        # Check for complex effects like 'increase'
        if eff[0] in ["increase", 'decrease', 'assign']:
            effected_var = str_var_dict[list2var_str(eff[1])]
            effect_details = compile_expression(eff, str_var_dict)
            params = tuple([x for x in get_atoms(effect_details) if not z3_identical(x, effected_var)])
            effect_type = EffectTypePDDL(effected_var, effect_details, params=params)
            effect_types.append(effect_type)
        else:
            effected_var = compile_expression(eff, str_var_dict)
            # This may accidentally cause different EfectTypes to be identified bc True == 1.
            effect_details = True
            effect_type = EffectTypePDDL(effected_var, effect_details)
            effect_types.append(effect_type)
    # Assume for now that del_effects only sets bools to false
    for eff in a.del_effects:
        effected_var = compile_expression(eff, str_var_dict)
        # This may accidentally cause different EfectTypes to be identified bc True == 1.        
        effect_details = False
        effect_type = EffectTypePDDL(effected_var, effect_details)
        effect_types.append(effect_type)
    return tuple(effect_types)


if __name__ == '__main__':
    # zeno_dom = "examples/zeno/zeno.pddl"
    # zeno_prob = "examples/zeno/pb1.pddl"
    # domain, problem = zeno_dom, zeno_prob

    taxi_dom = "examples/taxi-numeric/taxi-domain.pddl"
    taxi_prob = "examples/taxi-numeric/prob02.pddl"
    domain, problem = taxi_dom, taxi_prob

    parser = PDDL_Parser()
    parser.parse_domain(domain)
    parser.parse_problem(problem)

    # str2var_dict after this contains a mapping of 
    # str -> z3 var
    str2var_dict = OrderedDict()
    str2var_dict = make_z3_atoms(parser.predicates, z3.Bool, str2var_dict)
    str2var_dict = make_z3_atoms(parser.functions, z3.Int, str2var_dict)

    # str_grounded_actions now contains a list of all possible actions grounded to 
    # all possible objects 
    str_grounded_actions = [parser.get_action_groundings(a) for a in parser.actions]

    # This below block creates all skills (CAE Triples) for the domain!
    skill_list = []
    for action_class in str_grounded_actions:
        for grounded_action in action_class:
            precond = action2precondition(grounded_action, str2var_dict)
            effect_types = action2effect_types(grounded_action, str2var_dict)
            skill = SkillPDDL(precond, grounded_action.name, effect_types)
            skill_list.append(skill)

    # This below block converts all the domain's goals to z3
    goal_list = [compile_expression(pos_goal_expr, str2var_dict) for pos_goal_expr in parser.positive_goals]
    goal_list += [z3.Not(compile_expression(neg_goal_expr, str2var_dict)) for neg_goal_expr in parser.negative_goals]
    goal_cond = z3.And(*goal_list)

    # This below block converts all the domain's initial conditions to z3
    init_cond_list = [compile_expression(init_cond, str2var_dict) for init_cond in parser.state]

    # Run the scoper on the constructed goal, skills and initial condition
    rel_pvars, rel_skills = scope(goals=goal_cond, skills=skill_list, start_condition=init_cond_list)
    print("~~~~~Relevant pvars~~~~~")
    for p in rel_pvars:
        print(p)
    print("~~~~~Relevant skills~~~~~")
    print("\n\n".join([str(s) for s in rel_skills]))
    print(len(skill_list), len(rel_skills))
    # print(rel_pvars)
    # print(rel_skills)

