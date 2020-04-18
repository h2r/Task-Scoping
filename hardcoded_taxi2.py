import z3
from classes import *
import pdb
from typing import List
from typing import NamedTuple

class Passenger(NamedTuple):
	name: int
	y: z3.Int
	intaxi: z3.Bool

class Taxi(NamedTuple):
	name: int
	y: z3.Int

# NOTE: We assume we only have 1 taxi.

def make_passengers(n=2):
	passengers = []
	for i in range(n):
		name = f'p{i}'
		intaxi = z3.Bool(f'passenger-in-taxi({name},t0)')
		y = z3.Int(f'passenger-y-curr({name})')
		p = Passenger(name, y, intaxi)
		passengers.append(p)
	return passengers

def make_taxis(n=1):
	taxis = []
	for i in range(n):
		name = f"t{i}"
		y = z3.Int(f"taxi-y({name})")
		taxis.append(Taxi(name, y))
	return taxis

def make_movement_skills(passengers: List[Passenger], taxi:Taxi, action_name, var_affected):
	skills = []
	# 	Empty Taxi
	cond = z3.And(*[z3.Not(p.intaxi) for p in passengers])
	effect = [getattr(taxi, var_affected)]
	skills.append(Skill(cond, action_name, effect))

	# 	Passenger in taxi
	for i, p in enumerate(passengers):
		conds = [p.intaxi]
		for i1, p1 in enumerate(passengers):
			if i1 != i:
				conds.append(z3.Not(p1.intaxi))
		cond = z3.And(*conds)
		effect = [getattr(taxi, var_affected), getattr(p, var_affected)]
		skills.append(Skill(cond, action_name, effect))
	return skills


def make_initial_condition(passengers: List[Passenger], taxi: Taxi):
	cond = z3.And(*[z3.Not(p.intaxi) for p in passengers])
	return cond

def make_goal(passenger, x = None, y = None):
	conds = [z3.Not(passenger.intaxi)]
	if x is not None: conds.append(passenger.x == x)
	if y is not None: conds.append(passenger.y == y)
	return z3.And(conds)

def prepare_taxi_domain(n_passegners = 2):
	"""Returns skills, init_cond, goal"""
	passengers =  make_passengers(n_passegners)
	taxi = make_taxis(1)[0]
	move_north = make_movement_skills(passengers, taxi, "move_north()", 'y')
	move_south = make_movement_skills(passengers, taxi, "move_south()", 'y')
	skills = move_north + move_south
	start_condition = make_initial_condition(passengers, taxi)
	goal = make_goal(passengers[0], y = 3)
	pvars = [taxi.y] + [p.y for p in passengers] + [p.intaxi for p in passengers]
	return goal, skills, start_condition, pvars
	# return pas



if __name__ == "__main__":
	passengers =  make_passengers(2)
	taxi = make_taxis(1)[0]
	move_north = make_movement_skills(passengers, taxi, "move_north()", 'y')
	move_south = make_movement_skills(passengers, taxi, "move_south()", 'y')

# for s in move_north: print(s)