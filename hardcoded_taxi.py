import copy
import z3
from classes import *
from scoping import *
from instance_building_utils import *
from logic_utils import and2

# TODO add asserts
# TODO rewrite so that [north, south, east, west] always come in same order to reduce chance of bugs. NSEW seams best, since it groups x,y
# TODO finish refactoring to use g2v
def object_counts_to_names(object_counts):
	object_names = {}
	for k, v in object_counts.items():
		object_names[k] = [type_and_id2name(k,i) for i in range(v)]
	return object_names

def set_init_state_and_constants(solver, object_counts, g2v):
	passengers_you_care_for_value_list = [True] + [False for _ in range(object_counts['passenger'] - 1)]
	passenger_goal_x_values = [2, 3]
	passenger_goal_y_values = [3, 2]
	passenger_start_x_values = [1, 1]
	passenger_start_y_values = [3, 1]
	for p_id in range(object_counts['passenger']):
		solver.add(g2v('PASSENGERS_YOU_CARE_FOR', [p_id]) == passengers_you_care_for_value_list[p_id])
		solver.add(g2v("PASSENGER_GOAL_X", [p_id]) == passenger_goal_x_values[p_id])
		solver.add(g2v("PASSENGER_GOAL_Y", [p_id]) == passenger_goal_y_values[p_id])
		solver.add(g2v("passenger-x-curr", [p_id]) == passenger_start_x_values[p_id])
		solver.add(g2v("passenger-y-curr", [p_id]) == passenger_start_y_values[p_id])
		for t_id in range(object_counts['taxi']):
			solver.add(g2v('passenger-in-taxi', [p_id, t_id]) == False)
	solver.add(g2v('taxi-x', [0]) == 0)
	solver.add(g2v('taxi-y', [0]) == 0)
	# solver.add(g2v('WALL_X',[0]) == 0)
	# solver.add(g2v('WALL_Y',[0]) == 1)
	assert solver.check() == z3.sat
	# print(solver.assertions())
	solver.push()
def create_no_touch_conditions(object_counts, g2v):
	"""
	:param object_counts:
	:return: [t_id][nesw] list of no_touch conditions
	"""
	notouch_by_taxi = []
	for t_id in range(object_counts['taxi']):
		wall_x_groundings = wall_x.ground(all_object_names)
		wall_y_groundings = wall_y.ground(all_object_names)
		wall_touch_north_list = []
		wall_touch_south_list = []
		wall_touch_east_list = []
		wall_touch_west_list = []
		# For each wall, create Precondition about its northess, southness, etc. from taxi
		for w_id in range(object_counts['wall']):
			w_x = wall_x_groundings[w_id]
			w_y = wall_y_groundings[w_id]
			# Pycharm complained about typechecking here; the noinspection comments disable that
			same_x = (g2v('taxi-x', [t_id]) == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			east_x = (g2v('taxi-x', [t_id]) + 1 == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			west_x = (g2v('taxi-x', [t_id]) - 1 == name_to_z3_var[w_x])
			same_y = (g2v('taxi-y', [t_id]) == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			north_y = (g2v('taxi-y', [t_id]) + 1 == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			south_y = (g2v('taxi-y', [t_id]) - 1 == name_to_z3_var[w_y])

			wall_touch_north_list.append(z3.And(same_x, north_y))
			wall_touch_east_list.append(z3.And(east_x, same_y))
			wall_touch_south_list.append(z3.And(same_x, south_y))
			wall_touch_west_list.append(z3.And(west_x, same_y))
		# Combine touch conditions from each wall to get overall touch conditions
		no_touch_north_condition = z3.Not(z3.Or(*wall_touch_north_list))
		no_touch_east_condition = z3.Not(z3.Or(*wall_touch_east_list))
		no_touch_south_condition = z3.Not(z3.Or(*wall_touch_south_list))
		no_touch_west_condition = z3.Not(z3.Or(*wall_touch_west_list))
		notouch_this_taxi = [no_touch_north_condition,no_touch_east_condition,no_touch_south_condition,no_touch_west_condition]
		notouch_by_taxi.append(notouch_this_taxi)
	return notouch_by_taxi

def make_skills(object_counts, g2n, g2v):
	skill_triples = []
	notouch_by_taxi = create_no_touch_conditions(object_counts, g2v)
	for t_id in range(object_counts['taxi']):
		taxi_empty_vars = [z3.Not(g2v('passenger-in-taxi',[p_id,t_id])) for p_id in range(object_counts['passenger'])]
		taxi_empty_condition = AndList(*taxi_empty_vars)
		# Create not-touching wall conditions
		no_touch_north_condition, no_touch_east_condition, no_touch_south_condition, no_touch_west_condition = notouch_by_taxi[t_id]
		# Add skills for each movement direction
		skill_triples.append(
			Skill(no_touch_north_condition, "move_north_{}".format(t_id), ['taxi-y_{}'.format(t_id)]))
		skill_triples.append(
			Skill(no_touch_south_condition, "move_south_{}".format(t_id), ['taxi-y_{}'.format(t_id)]))
		skill_triples.append(
			Skill(no_touch_east_condition, "move_east_{}".format(t_id), ['taxi-x_{}'.format(t_id)]))
		skill_triples.append(
			Skill(no_touch_west_condition, "move_west_{}".format(t_id), ['taxi-x_{}'.format(t_id)]))

		# Create single-passenger-in-taxi conditions, and pickup/dropoff
		for p_id in range(object_counts['passenger']):
			# passenger_in_taxi_conditions = []
			# for p_id2 in range(object_counts['passenger']):
			# 	if p_id2 == p_id:
			# 		passenger_in_taxi_conditions.append(g2v('passenger-in-taxi',[p_id]))
			# 	# We don't need to mention the other passengers, but it doesn't hurt. Consider rewriting this bit.
			# 	else:
			# 		passenger_in_taxi_conditions.append(z3.Not(g2v('passenger-in-taxi',[p_id2])))
			# taxi_occupance_condition = AndList(*passenger_in_taxi_conditions)
			taxi_occupance_condition = g2v('passenger-in-taxi', [p_id, 0])
			#  Combine passenger in taxi Precondition with no_touch conditions
			move_north_with_passenger_condition = and2(no_touch_north_condition, taxi_occupance_condition)
			move_east_with_passenger_condition = and2(no_touch_east_condition, taxi_occupance_condition)
			move_south_with_passenger_condition = and2(no_touch_south_condition, taxi_occupance_condition)
			move_west_with_passenger_condition = and2(no_touch_west_condition, taxi_occupance_condition)

			skill_triples.append(Skill(move_north_with_passenger_condition, "move_north_{}".format(t_id),
									   [g2n('passenger-y-curr',[p_id])]))
			skill_triples.append(Skill(move_south_with_passenger_condition, "move_south_{}".format(t_id),
									   [g2n('passenger-y-curr',[p_id])]))
			skill_triples.append(Skill(move_east_with_passenger_condition, "move_east_{}".format(t_id),
									   [g2n('passenger-x-curr',[p_id])]))
			skill_triples.append(Skill(move_west_with_passenger_condition, "move_west_{}".format(t_id),
									   [g2n('passenger-x-curr',[p_id])]))

			# Add pickup actions
			shared_x_condition = (g2v('taxi-x', [t_id]) == g2v('passenger-x-curr', [p_id]))
			shared_y_condition = (g2v('taxi-y', [t_id]) == g2v('passenger-y-curr', [p_id]))
			pickup_condition = AndList(shared_x_condition, shared_y_condition, taxi_empty_condition)
			dropoff_condition = g2v('passenger-in-taxi',[p_id,t_id])
			skill_triples.append(
				Skill(pickup_condition, 'pickup_{}_{}'.format(t_id, p_id), [g2n('passenger-in-taxi', [p_id, t_id])]))
			skill_triples.append(
				Skill(dropoff_condition, "dropoff_{}_{}".format(t_id, p_id), [g2n('passenger-in-taxi', [p_id, t_id])]))
	return skill_triples

if __name__ == "__main__":
	types = ['taxi', 'passenger', 'wall']
	actions = [
		DomainAction("move_north", ['taxi']),
		DomainAction("move_south", ['taxi']),
		DomainAction("move_east", ['taxi']),
		DomainAction("move_west", ['taxi']),
		DomainAction("pickup", ["taxi", "passenger"]),
		DomainAction("dropoff", ["taxi", "passenger"])
	]
	object_counts = {
		"passenger": 2,
		"taxi": 1,
		"wall": 0
	}
	all_object_names = object_counts_to_names(object_counts)

	# Constants
	constants = [
		DomainAttribute('WALL_X', z3.Int, ['wall']),
		DomainAttribute('WALL_Y', z3.Int, ['wall']),
		DomainAttribute('PASSENGER_GOAL_X', z3.Int, ['passenger']),
		DomainAttribute('PASSENGER_GOAL_Y', z3.Int, ['passenger']),
		DomainAttribute('PASSENGERS_YOU_CARE_FOR',z3.Bool,['passenger']),
		DomainAttribute('MAX_X', z3.Int, []),
		DomainAttribute('MAX_Y', z3.Int, [])
	]
	wall_x, wall_y, passenger_goal_x, passenger_goal_y, passengers_you_care_for, max_x, max_y = constants
	# We should get the this < 10 constraints from the MAX_X, MAX_Y constants
	attributes = [
		DomainAttribute('taxi-x', z3.Int, ['taxi'], ["0 < this", "this < 10"]),
		DomainAttribute('taxi-y', z3.Int, ['taxi'], ["0 < this", "this < 10"]),

		DomainAttribute('passenger-x-curr', z3.Int, ['passenger'], ["0 < this", "this < 10"]),
		DomainAttribute('passenger-y-curr', z3.Int, ['passenger'], ["0 < this", "this < 10"]),
		DomainAttribute('passenger-in-taxi', z3.Bool, ['passenger', 'taxi'])
	]
	taxi_x, taxi_y, passenger_x_curr, passenger_y_curr, passenger_in_taxi = attributes

	# z3 stuff
	# Define propositions
	name_to_z3_var = {}

	for att in attributes + constants:
		grounded_attributes = att.ground(all_object_names)
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			print(g)
			# Apply constraints
			pass
	g2n = g2n_builder(attributes + constants + actions)
	g2v = g2v_builder(name_to_z3_var, g2n)
	solver = z3.Solver()
	# Assign constants and init state
	set_init_state_and_constants(solver, object_counts, g2v)

	# Make skill triples
	skill_triples = make_skills(object_counts, g2n, g2v)
	# Create goal Precondition. For now, we are using explicit goal Precondition rather than a more general reward
	at_goal_or_unimportant_conditions = []
	for p_id in range(object_counts['passenger']):
		cur_x_var = g2v('passenger-x-curr', [p_id])
		cur_y_var = g2v('passenger-y-curr', [p_id])
		goal_x_var = g2v('PASSENGER_GOAL_X', [p_id])
		goal_y_var = g2v('PASSENGER_GOAL_Y', [p_id])
		at_goal_condition = ((cur_x_var == goal_x_var) and (cur_y_var == goal_y_var))
		at_goal_or_unimportant_conditions.append(z3.Or(at_goal_condition, z3.Not(g2v('PASSENGERS_YOU_CARE_FOR', [p_id]))))
	# Since this condition includes each passenger's location in an OR, the scoper thinks they are relevant
	# We can fix this by plugging in constants to expressions and simplifying, but for now I will define an easier goal
	goal_condition_hard_to_parse = AndList(*at_goal_or_unimportant_conditions)
	cared_for_goal_conditions = []
	#Checking this assertion in the loop raises an s
	assert solver.check() == z3.z3.sat
	#The above goal condition is hard to parse b.c. it mentions irrelevant passengers. The below version is easier to use
	for p_id in range(object_counts['passenger']):
		result = solver.check()
		assert result == z3.z3.sat, result
		#Check whether we care for the passenger
		solver.push()
		# If the passenger cannot not be cared for, they are cared for
		solver.add(g2v('PASSENGERS_YOU_CARE_FOR', [p_id]) == False)
		result = solver.check()
		solver.pop()
		if result == z3.z3.unsat:
			cur_x_var = g2v('passenger-x-curr', [p_id])
			cur_y_var = g2v('passenger-y-curr', [p_id])
			goal_x_var = g2v('PASSENGER_GOAL_X', [p_id])
			goal_y_var = g2v('PASSENGER_GOAL_Y', [p_id])
			at_goal_condition = z3.And((cur_x_var == goal_x_var), (cur_y_var == goal_y_var))
			cared_for_goal_conditions.append(at_goal_condition)
	goal_condition_easy_to_parse = AndList(cared_for_goal_conditions)

	dgb = solver_implies_condition(solver,z3.Not(g2v('PASSENGER_GOAL_Y',[0]) == g2v("passenger-y-curr",[0])))
	print("Y goal implied: {}".format(dgb))
	# goal_condition = Precondition()
	# Test whether start state implies skills
	# for skill in skill_triples:
	# 	pass
		# print("Action: {}".format(skill.get_action()))
		# print("Affected variables: {}".format(skill.get_targeted_variables()))
		# guaranteed = solver_implies_condition(solver, skill.get_precondition())
		# print("Precondition guaranteed: {}".format(guaranteed))
	# x = z3.z3util.get_vars(goal_z3)
	# y = x[0]
	# print(x)
	# print(y)

#Run scoping
	correct_vars = [g2n('taxi-y',[0]),g2n('taxi-x',[0]), g2n('passenger-in-taxi',[0,0]), g2n('passenger-x-curr',[0]),g2n('passenger-y-curr',[0]),g2n('PASSENGER_GOAL_X',[0]),g2n('PASSENGER_GOAL_Y',[0])]
	correct_vars.sort()
	print("correct vars:")
	print(correct_vars)
	print("Scoping")
	discovered_not_guarantees, used_skills = scope(goal_condition_easy_to_parse,skill_triples,solver=solver)
	discovered_not_guarantees.sort()
	missing = [i for i in correct_vars if i not in discovered_not_guarantees]
	extra = [i for i in discovered_not_guarantees if i not in correct_vars]
	print(discovered_not_guarantees)
	print("Missing: {}".format(missing))
	print("Extra: {}".format(extra))