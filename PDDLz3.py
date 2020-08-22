from PDDL import PDDL_Parser, Action
import z3
from collections import OrderedDict
from skill_classes import EffectTypePDDL, SkillPDDL
from utils import product_dict, nested_list_replace, get_atoms
from typing import List, Tuple, Dict, Iterable

class PDDL_Parser_z3(PDDL_Parser):
    def make_z3_atoms(self, things_dict, z3_class, str2var = None):
        """
        things_dict should be parser.predicates or parser.functions
        z3_class should be z3.Bool or z3.Int
        str2var is the dictionary you want to update. If none, a new OrderedDict is created
        """
        if str2var is None:
            str2var = OrderedDict()
        for p_name, p_args in things_dict.items():
            groundings = product_dict(**OrderedDict([(varnm, self.get_objects_of_type(vartype)) for (varnm, vartype) in p_args.items()]))
            for x in groundings:
                s = p_name + "(" + ", ".join(x.values()) + ")"
                grounded_predicate = z3_class(s)
                assert s not in str2var.keys(), f"{s}: {str2var[s]}, {grounded_predicate}"
                str2var[s] = grounded_predicate
        return str2var
    
    def make_str2var_dict(self):
        str2var_dict = OrderedDict()
        str2var_dict = self.make_z3_atoms(self.predicates, z3.Bool, str2var_dict)
        str2var_dict = self.make_z3_atoms(self.functions, z3.Int, str2var_dict)
        return str2var_dict

    def str_grounded_actions2skills(self, str_grounded_actions, str2var_dict):
        skill_list = []
        for action_class in str_grounded_actions:
            for grounded_action in action_class:
                precond = self.action2precondition(grounded_action, str2var_dict)
                effect_types = action2effect_types(grounded_action, str2var_dict)
                skill = SkillPDDL(precond, grounded_action.name, effect_types)
                skill_list.append(skill)
        return skill_list
    def action2precondition(self, a: Action, str_var_dict) -> z3.BoolRef:
        clauses = [compile_expression(p, str_var_dict, parser=self) for p in a.positive_preconditions] + [z3.Not(compile_expression(p, str_var_dict, parser=self)) for p in a.negative_preconditions]
        return z3.And(*clauses)
    def get_skills(self):
        str2var_dict = self.make_str2var_dict()
        str_grounded_actions = [self.get_action_groundings(a) for a in self.actions]
        skill_list = self.str_grounded_actions2skills(str_grounded_actions, str2var_dict)
        return skill_list
    def get_goal_cond(self):
        str2var_dict = self.make_str2var_dict()
        goal_list = [compile_expression(pos_goal_expr, str2var_dict, self) for pos_goal_expr in self.positive_goals]
        goal_list += [z3.Not(compile_expression(neg_goal_expr, str2var_dict, self)) for neg_goal_expr in self.negative_goals]
        goal_cond = z3.And(*goal_list)
        return goal_cond
    def get_init_cond_list(self):
        str2var_dict = self.make_str2var_dict()
        return [compile_expression(init_cond, str2var_dict, self) for init_cond in self.state]

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



def z3_identical(a, b):
    return a.sort() == b.sort() and str(a) == str(b)



def compile_expression(expr, str_var_dict, parser=None):

    """ 
    :param expr - a (potentially nested) list of strings. Should be grounded to objects, except for quantified predicates
    :param str_var_dict - a dictionary mapping strings representing pvars to their corresponding z3 objects
    :param parser - a PDDL_Parser. Only needed to ground quantified objects
    """
    if isinstance(expr, int):
        return expr
    elif isinstance(expr, str):
        # the only str we can interpret in a vacuum is an int. (maybe bools later?)
        try:
            expr = int(expr)
            return expr
        except ValueError as e:
            from IPython import embed; embed() #What is embed?
            raise e
    elif isinstance(expr, list):
        # A flat list corresponds to a pvar
        if list_is_flat(expr):
            return str_var_dict[list2var_str(expr)]
        elif len(expr) == 2:
            # The only length 2 expression we can compile is ['not', [subexpression]]
            if expr[0] == "not":
                return z3.Not(compile_expression(expr[1], str_var_dict))
            else:
                raise ValueError(f"Don't understand how to compile: {expr}")
        else:
            assert len(expr) == 3, f"Don't understand how to compile: {expr}"
            # Handle quantifiers. It is a bit odd that we ground quantifiers here, not during grounding
                # Example quantifier: ['forall', ['?pn', '-', 'passenger'], ['not', ['passenger-in-taxi', '?pn', '?t']]]]
            if expr[0] in ["forall", "exists"]:
                quantifier, quantified_var, subexpr = expr
                varnm, vartype = quantified_var[0], quantified_var[2]
                # Get all groundings for the quantified object
                var_groundings = parser.get_objects_of_type(vartype)
                # Get all grounded versions of the subexpression
                subexpr_groundings = [nested_list_replace(subexpr, {varnm: x}) for x in var_groundings]
                # Compile the grounded subexpressions
                compiled_subexpressions = [compile_expression(x, str_var_dict) for x in subexpr_groundings]
                # Combine the compiled subexpressions
                combinator = {"forall":z3.And, "exists":z3.Or}[quantifier]
                return combinator(*compiled_subexpressions)
            # Handle operations
            else:
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
    


def str_grounded_actions2skills(str_grounded_actions, str2var_dict):
    skill_list = []
    for action_class in str_grounded_actions:
        for grounded_action in action_class:
            precond = action2precondition(grounded_action, str2var_dict)
            effect_types = action2effect_types(grounded_action, str2var_dict)
            skill = SkillPDDL(precond, grounded_action.name, effect_types)
            skill_list.append(skill)
    return skill_list

if __name__ == "__main__":
    domain, problem = "./examples/existential-taxi/taxi-domain.pddl", "./examples/existential-taxi/prob02.pddl"
    parser = PDDL_Parser_z3()
    parser.parse_domain(domain)
    parser.parse_problem(problem)
    skills = parser.get_skills()
    print("\n\n".join(map(str,skills)))