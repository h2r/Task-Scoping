import z3
from skill_classes import EffectType, Skill
import pdb
from typing import List
from typing import NamedTuple
# TODO incorporate EffectTypes
# TODO add pickup/dropoff

class Passenger(NamedTuple):
	name: int
	x: z3.Int
	y: z3.Int
	intaxi: z3.Bool


class Taxi(NamedTuple):
	name: int
	x: z3.Int
	y: z3.Int
	blinker: z3.Bool

# NOTE: We assume we only have 1 taxi.

def make_passengers(n=2):
	passengers = []
	for i in range(n):
		name = f'p{i}'
		intaxi = z3.Bool(f'passenger-in-taxi({name},t0)')
		x = z3.Int(f'passenger-x-curr({name})')
		y = z3.Int(f'passenger-y-curr({name})')
		p = Passenger(name, x, y, intaxi)
		passengers.append(p)
	return passengers


def make_taxis(n=1):
	taxis = []
	for i in range(n):
		name = f"t{i}"
		x = z3.Int(f"taxi-x({name})")
		y = z3.Int(f"taxi-y({name})")
		blinker = z3.Bool(f"taxi-blinker({name})")
		taxis.append(Taxi(name, x, y, blinker))
	return taxis


def make_movement_skills(passengers: List[Passenger], taxi: Taxi, action_name, var_affected, blinker=False,
						 blinker_affects=None):
	skills = []
	# 	Empty Taxi
	cond = z3.And(*[z3.Not(p.intaxi) for p in passengers])
	effect = [EffectType(getattr(taxi, var_affected),0)]
	if blinker:
		cond_b_off = z3.And(cond, z3.Not(taxi.blinker))
		cond_b_on = z3.And(cond, taxi.blinker)
		effect_b_off = effect
		effect_b_on = effect + [EffectType(getattr(taxi, blinker_affects),0)]
		skills.append(Skill(cond_b_off, action_name, effect_b_off))
		skills.append(Skill(cond_b_on, action_name, effect_b_on))
	else:
		skills.append(Skill(cond, action_name, effect))
	# 	Passenger in taxi
	for i, p in enumerate(passengers):
		conds = [p.intaxi]
		for i1, p1 in enumerate(passengers):
			if i1 != i:
				conds.append(z3.Not(p1.intaxi))
		cond = z3.And(*conds)
		effect = [EffectType(getattr(taxi, var_affected),0), EffectType(getattr(p, var_affected),0)]
		if blinker:
			cond_b_off = z3.And(cond, z3.Not(taxi.blinker))
			cond_b_on = z3.And(cond, taxi.blinker)
			effect_b_off = effect
			effect_b_on = effect + [EffectType(getattr(taxi, blinker_affects),0), EffectType(getattr(p, blinker_affects),0)]
			skills.append(Skill(cond_b_off, action_name, effect_b_off))
			skills.append(Skill(cond_b_on, action_name, effect_b_on))
		else:
			skills.append(Skill(cond, action_name, effect))
	return skills


def make_initial_condition(passengers: List[Passenger], taxi: Taxi):
	cond = z3.And(*([z3.Not(p.intaxi) for p in passengers] + [taxi.blinker]))
	return cond


def make_goal(passenger, x=None, y=None):
	conds = [z3.Not(passenger.intaxi)]
	if x is not None: conds.append(passenger.x == x)
	if y is not None: conds.append(passenger.y == y)
	return z3.And(conds)


def prepare_taxi_domain(n_passegners=2, blinker = False, goal = (6, 8)):
	"""Returns skills, init_cond, goal"""
	# if blinker:
	# 	blinker_affects = {"move_north()": "x", "move_south()": "x", "move_east()":"y", "move_west()":"y"}
	passengers = make_passengers(n_passegners)
	taxi = make_taxis(1)[0]
	move_north = make_movement_skills(passengers, taxi, "move_north()", 'y', blinker, 'x')
	move_south = make_movement_skills(passengers, taxi, "move_south()", 'y', False, 'x')
	move_east = make_movement_skills(passengers, taxi, "move_east()", 'x', False, 'y')
	move_west = make_movement_skills(passengers, taxi, "move_west", 'x', False, 'y')
	skills = move_north + move_south + move_east + move_west
	start_condition = make_initial_condition(passengers, taxi)
	goal = make_goal(passengers[0], x=goal[0], y=goal[1])
	pvars = [taxi.y] + [p.y for p in passengers] + [p.intaxi for p in passengers]
	return goal, skills, start_condition, pvars


# return pas


if __name__ == "__main__":
	passengers = make_passengers(2)
	taxi = make_taxis(1)[0]
	move_north = make_movement_skills(passengers, taxi, "move_north()", 'y')
	move_south = make_movement_skills(passengers, taxi, "move_south()", 'y')

# for s in move_north: print(s)