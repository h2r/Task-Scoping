from oo_scoping.PDDL import PDDL_Parser, Action
import z3, re
from collections import OrderedDict
from oo_scoping.skill_classes import EffectTypePDDL, SkillPDDL
from oo_scoping.utils import product_dict, nested_list_replace, get_atoms, get_unique_z3_vars
from typing import List, Tuple, Dict, Iterable

import sas_tasks

def make_str2var_dict(sas_vars):
    """
    Returns a dict of str(var_names) -> z3Var(var_names)

    Input: a SASVariables Object corresponding to all the variables in this particular problem
    Output: a new dictionary mapping var_name strings to z3 vars that are created for each variable

    """
    str2var = OrderedDict()
    for i in range(len(sas_vars.ranges)):
        if sas_vars.ranges[i] == 2:
            z3_func = z3.Bool
        elif sas_vars.ranges[i] > 2:
            z3_func = z3.Int
        else:
            print("There's some SAS+ variable with a domain of 0 or 1. We probably can handle this by just treating this as a Bool, but \
                I'm setting a breakpoint here just in case so you're aware of this variable and there's no silent failure...")
            from IPython import embed; embed()
            exit(1)
        var_str = "v"+str(i)
        z3_var = z3_func(var_str)
        str2var[var_str] = z3_var

    return str2var
