import z3
from classes import *
import instance_building_utils
import pdb
from typing import List, Dict, Tuple
from logic_utils import solver_implies_condition, OrList, or2, and2, get_iff, get_var_names, synth2varnames, AndList, not2

# This function returns goal_conditions, necessarily_relevant_pvars, skill_triplets, solver
# that are necessary for the scoping algorithm
def prepare_1D_taxi():
    pass

def make_skills():
    # All pvars_over_objects
    p0_intaxi = z3.Bool('passenger-in-taxi(p0,t0)')
    p1_intaxi = z3.Bool('passenger-in-taxi(p1,t0)')
    taxi_y = z3.Int('taxi-y(t0)')
    p0_y = z3.Int('passenger-y-curr(p0)')
    p1_y = z3.Int('passenger-y-curr(p1)')

    pvar_to_effect_types = {}

    # skill 1: (Not p1.in_taxi & Not p0.in_taxi, move_north, taxi_y++)
    s1_precond = AndList(*[z3.Not(p0_intaxi), z3.Not(p1_intaxi)])
    s1_action = "move_north()"
    s1_effect = [taxi_y]
    s1 = Skill(s1_precond, s1_action, s1_effect)

    # skill 2: (Not p1.in_taxi & p0.in_taxi, move_north, taxi_y++ & p0.y ++)
    s2_precond = AndList(*[p0_intaxi, z3.Not(p1_intaxi)])
    s2_action = "move_north()"
    s2_effect = [taxi_y, p0_y]
    s2 = Skill(s2_precond, s2_action, s2_effect)

    # skill 3: (p1.in_taxi & Not p0.in_taxi, move_north, taxi_y++ & p1.y ++)
    s3_precond = AndList(*[z3.Not(p0_intaxi), p1_intaxi])
    s3_action = "move_north()"
    s3_effect = [taxi_y, p1_y]
    s3 = Skill(s3_precond, s3_action, s3_effect)

    # skill 4: (Not p1.in_taxi & Not p0.in_taxi, move_south, taxi_y--)
    s4_precond = AndList(*[z3.Not(p0_intaxi), z3.Not(p1_intaxi)])
    s4_action = "move_south()"
    s4_effect = [taxi_y]
    s4 = Skill(s4_precond, s4_action, s4_effect)

    # skill 5: (Not p1.in_taxi & p0.in_taxi, move_south, taxi_y-- & p0.y--)
    s5_precond = AndList(*[p0_intaxi, z3.Not(p1_intaxi)])
    s5_action = "move_south()"
    s5_effect = [taxi_y, p0_y]
    s5 = Skill(s5_precond, s5_action, s5_effect)

    # skill 6: (p1.in_taxi & Not p0.in_taxi, move_south, taxi_y-- & p1.y--)
    s6_precond = AndList(*[z3.Not(p0_intaxi), p1_intaxi])
    s6_action = "move_south()"
    s6_effect = [taxi_y, p1_y]
    s6 = Skill(s6_precond, s6_action, s6_effect)

    # skill 7 (Not(p1.intaxi) & Not(p0.intaxi) & (p0.y == taxi.y), pickup(p0), p0.intaxi)
    s7_precond = AndList(*[z3.Not(p0_intaxi), z3.Not(p1_intaxi), taxi_y == p0_y])
    s7_action = "pickup(p0)"
    s7_effect = [p0_intaxi]
    s7 = Skill(s7_precond, s7_action, s7_effect)

    # skill 8 (Not(p1.intaxi) & Not(p0.intaxi) & (p1.y == taxi.y), pickup(p1), p1.intaxi)
    s8_precond = AndList(*[z3.Not(p0_intaxi), z3.Not(p1_intaxi), taxi_y == p1_y])
    s8_action = "pickup(p1)"
    s8_effect = [p1_intaxi]
    s8 = Skill(s8_precond, s8_action, s8_effect)

    # skill 9 (Not(p1.intaxi) & p0.intaxi, dropoff(p0), p0.intaxi)
    s9_precond = AndList(*[p0_intaxi, z3.Not(p1_intaxi)])
    s9_action = "dropoff(p0)"
    s9_effect = [p0_intaxi]
    s9 = Skill(s9_precond, s9_action, s9_effect)

    # skill 10 (p1.intaxi & Not(p0.intaxi), dropoff(p1), p1.intaxi)
    s10_precond = AndList(*[p1_intaxi, z3.Not(p0_intaxi)])
    s10_action = "dropoff(p1)"
    s10_effect = [p1_intaxi]
    s10 = Skill(s10_precond, s10_action, s10_effect)

    # Add the correct effect type sets to a dictionary keyed by the pvar-over-objects
    # There is one key for each pvar
    pvar_to_effect_types[taxi_y] = [[s1, s2, s3], [s4, s5, s6]]
    pvar_to_effect_types[p0_intaxi] = [[s7], [s9]]
    pvar_to_effect_types[p1_intaxi] = [[s8], [s10]]
    pvar_to_effect_types[p0_y] = [[s2], [s5]]
    pvar_to_effect_types[p1_y] = [[s3], [s6]]

    return pvar_to_effect_types

print(make_skills())