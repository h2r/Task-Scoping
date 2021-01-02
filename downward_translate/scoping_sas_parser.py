from oo_scoping.PDDL import PDDL_Parser, Action
import z3, re
from collections import OrderedDict
from oo_scoping.skill_classes import EffectTypePDDL, SkillPDDL
from oo_scoping.utils import product_dict, nested_list_replace, get_atoms, get_unique_z3_vars
from typing import List, Tuple, Dict, Iterable
from oo_scoping.action import Action

import sas_tasks

"""
General Notes on current implementation of SAS+ -> z3 for scoping purposes.

- All pvars are ints (this may not hold true for problems other than Monkeys)
- Actions only have "positive effects" as a result

"""


def make_str2var_dict(sas_vars):
    """
    Returns a dict of str(var_names) -> z3Var(var_names)

    Input: a SASVariables Object corresponding to all the variables in this particular problem
    Output: a new dictionary mapping var_name strings to z3 vars that are created for each variable

    Note: Currently, all variables are treated as z3.Ints. This is because SAS+ essentially treats everything as an enum.
    We could get bools by simply uncommenting the commented out block below, but will need to deal with this downstream.

    """
    str2var = OrderedDict()
    for i in range(len(sas_vars.ranges)):
    #     if sas_vars.ranges[i] == 2:
    #         z3_func = z3.Bool
    #     elif sas_vars.ranges[i] > 2:
    #         z3_func = z3.Int
    #     else:
    #         print("There's some SAS+ variable with a domain of 0 or 1. We probably can handle this by just treating this as a Bool, but \
    #             I'm setting a breakpoint here just in case so you're aware of this variable and there's no silent failure...")
    #         from IPython import embed; embed()
    #         exit(1)
        z3_func = z3.Int
        var_str = "v"+str(i)
        z3_var = z3_func(var_str)
        str2var[var_str] = z3_var

    return str2var

def make_str_grounded_actions(sas_ops):
    """
    Returns a list oo_scoping.action.Action variables

    Input: a list of SASOperator objects corresponding to all the actions in this particular problem
    Output: a non-nested list of oo_scoping.action.Action variables representing these operators

    TODO: Currently, we're not grouping the actions in any way (and it's unclear if we should), but this list
    might be a good place to do it if we wanted
    """
    list_of_actions = []
    for op in sas_ops:
        # First, parse out all the preconditions (including the one mentioned in the effect line)
        op_precond_list = op.get_applicability_conditions()
        action_precond_list = []
        for precond in op_precond_list:
            var_num, var_val = precond
            action_precond_list.append(['=',['v'+str(var_num)], str(var_val)])
        # Next, extract the effect
        pre_post_conds_list = op.pre_post
        action_effect_list = []
        for pre_post_cond in pre_post_conds_list:
            var_num, _, var_val, cond_list = pre_post_cond
            if len(cond_list) > 0:
                print("The pre_post cond of this operator has some cond list, and I haven't thought about \
                    what to do in the case where this is non-empty. Worth looking into")
                from IPython import embed; embed()
                exit(1)
            else:
                action_effect_list.append(['assign',['v'+str(var_num)], str(var_val)])
        # Finally construct an Action and append it to the list to be returned
        list_of_actions.append(Action(op.name,[],action_precond_list,[],action_effect_list,[]))
    return list_of_actions