import copy
import z3
from classes import *
from scoping import *


# TODO add asserts
#TODO rewrite so that [north, south, east, west] always come in same order to reduce chance of bugs. NSEW seams best, since it groups x,y
def object_counts_to_names(object_counts):
	object_names = {}
	for k, v in object_counts.items():
		object_names[k] = [str(i) for i in range(v)]
	return object_names


if __name__ == "__main__":
	types = ['taxi', 'passenger', 'wall']
	actions = [("move_north", 'taxi'), ("move_south", 'taxi'), ("move_east", 'taxi'), ("move_west", 'taxi'),
			("pickup", "taxi", "passenger"), ("dropoff", "taxi", "passenger")]
	# Constants
	non_fluents = [
		DomainAttribute('WALL_X', z3.Int, ['wall']),
		DomainAttribute('WALL_Y', z3.Int, ['wall']),
		DomainAttribute('PASSENGER_GOAL_X', z3.Int, ['passenger']),
		DomainAttribute('PASSENGER_GOAL_Y', z3.Int, ['passenger']),
		DomainAttribute('MAX_X', z3.Int, []),
		DomainAttribute('MAX_Y', z3.Int, [])
	]
	wall_x, wall_y, passenger_goal_x, passenger_goal_y, max_x, max_y = non_fluents
	# We should get the this < 10 constraints from the MAX_X, MAX_Y non_fluents
	attributes = [
		DomainAttribute('taxi-x', z3.Int, ['taxi'], ["0 < this", "this < 10"]),
		DomainAttribute('taxi-y', z3.Int, ['taxi'], ["0 < this", "this < 10"]),

		DomainAttribute('passenger-x-curr', z3.Int, ['passenger'], ["0 < this", "this < 10"]),
		DomainAttribute('passenger-y-curr', z3.Int, ['passenger'], ["0 < this", "this < 10"]),
		DomainAttribute('passenger-in-taxi', z3.Bool, ['passenger', 'taxi'])
	]
	taxi_x, taxi_y, passenger_x_curr, passenger_y_curr, passenger_in_taxi = attributes
	object_counts = {
		"passenger": 2,
		"taxi": 1,
		"wall": 0
	}
	# z3 stuff
	# Define propositions
	all_object_names = object_counts_to_names(object_counts)
	name_to_z3_var = {}

	for att in attributes:
		grounded_attributes = att.ground(all_object_names)
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			# Apply constraints
			pass
	solver = z3.Solver()
	# Define init state
	passengers_in_taxi_var_names = passenger_in_taxi.ground(all_object_names)
	for p in passengers_in_taxi_var_names:
		p_in_t_att = name_to_z3_var[p]
		solver.add(p_in_t_att == False)
	# solver.push()
	# Make skill triples
	skill_triples = []

	# Movement without passenger
	# Empty taxi condition
	object_names = {
		"passenger": [str(i) for i in range(object_counts["passenger"])]
	}
	for t in range(object_counts['taxi']):
		object_names["taxi"] = [str(t)]
		# Empty taxi condition
		passengers_in_taxi_var_names = passenger_in_taxi.ground(object_names)
		# for p in passengers_in_taxi_var_names: print(p)
		taxi_empty_vars = [z3.Not(name_to_z3_var[x]) for x in passengers_in_taxi_var_names]
		taxi_empty_condition = z3.And(*taxi_empty_vars)
		# Create not-touching wall conditions
		wall_x_groundings = wall_x.ground(all_object_names)
		wall_y_groundings = wall_y.ground(all_object_names)
		wall_touch_north_list = []
		wall_touch_south_list = []
		wall_touch_east_list = []
		wall_touch_west_list = []
		# For each wall, create condition about its northess, southness, etc. from taxi
		for w_id in range(object_counts['wall']):
			w_x = wall_x_groundings[w_id]
			w_y = wall_y_groundings[w_id]
			#Pycharm complained about typechecking here; the noinspection comments disable that
			same_x = (name_to_z3_var['taxi-x_{}'.format(t)] == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			east_x = (name_to_z3_var['taxi-x_{}'.format(t)] + 1 == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			west_x = (name_to_z3_var['taxi-x_{}'.format(t)] - 1 == name_to_z3_var[w_x])
			same_y = (name_to_z3_var['taxi-y_{}'.format(t)] == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			north_y = (name_to_z3_var['taxi-y_{}'.format(t)] + 1 == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			south_y = (name_to_z3_var['taxi-y_{}'.format(t)] - 1 == name_to_z3_var[w_y])

			wall_touch_north_list.append(z3.And(same_x,north_y))
			wall_touch_east_list.append(z3.And(east_x,same_y))
			wall_touch_south_list.append(z3.And(same_x,south_y))
			wall_touch_west_list.append(z3.And(west_x,same_y))
		#Combine touch conditions from each wall to get overall touch conditions
		no_touch_north_condition = z3.Not(z3.Or(*wall_touch_north_list))
		no_touch_east_condition = z3.Not(z3.Or(*wall_touch_east_list))
		no_touch_south_condition = z3.Not(z3.Or(*wall_touch_south_list))
		no_touch_west_condition = z3.Not(z3.Or(*wall_touch_west_list))
		#And no_touch conditions with empty passenger
		move_north_empty_condition = z3.And(no_touch_north_condition, taxi_empty_condition)
		move_east_empty_condition = z3.And(no_touch_east_condition, taxi_empty_condition)
		move_south_empty_condition = z3.And(no_touch_south_condition, taxi_empty_condition)
		move_west_empty_condition = z3.And(no_touch_west_condition, taxi_empty_condition)
		#Add skills for each movement direction with empty taxi
		skill_triples.append(SkillTriplet(move_north_empty_condition, "move_north_{}".format(t), ['taxi-y_{}'.format(t)]))
		skill_triples.append(SkillTriplet(move_south_empty_condition, "move_south_{}".format(t), ['taxi-y_{}'.format(t)]))
		skill_triples.append(SkillTriplet(move_east_empty_condition, "move_east_{}".format(t), ['taxi-x_{}'.format(t)]))
		skill_triples.append(SkillTriplet(move_west_empty_condition, "move_west_{}".format(t), ['taxi-x_{}'.format(t)]))

		# Create single-passenger-in-taxi conditions
		for p_id in range(len(passengers_in_taxi_var_names)):
			passenger_in_taxi_conditions = []
			for p_id2 in range(len(passengers_in_taxi_var_names)):
				p_inTaxi_name = passengers_in_taxi_var_names[p_id2]
				if p_id2 == p_id:
					passenger_in_taxi_conditions.append(name_to_z3_var[p_inTaxi_name])
				else:
					passenger_in_taxi_conditions.append(z3.Not(name_to_z3_var[p_inTaxi_name]))
			taxi_occupance_condition = z3.And(*passenger_in_taxi_conditions)
			#  Combine passenger in taxi condition with no_touch conditions
			move_north_with_passenger_condition = z3.And(no_touch_north_condition, taxi_occupance_condition)
			move_east_with_passenger_condition = z3.And(no_touch_east_condition, taxi_occupance_condition)
			move_south_with_passenger_condition = z3.And(no_touch_south_condition, taxi_occupance_condition)
			move_west_with_passenger_condition = z3.And(no_touch_west_condition, taxi_occupance_condition)

			skill_triples.append(SkillTriplet(move_north_with_passenger_condition, "move_north_{}".format(t),
											['taxi-y_{}'.format(t), 'passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_south_with_passenger_condition, "move_south_{}".format(t),
											['taxi-y_{}'.format(t), 'passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_east_with_passenger_condition, "move_east_{}".format(t),
											['taxi-x_{}'.format(t), 'passenger-y-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_west_with_passenger_condition, "move_west_{}".format(t),
											['taxi-x_{}'.format(t), 'passenger-y-curr_{}'.format(p_id)]))

		# Test whether start state implies skills
		for skill in skill_triples:
			print("Action: {}".format(skill.get_action()))
			print("Affected variables: {}".format(skill.get_affected_variables()))
			guaranteed = solver_implies_condition(solver, skill.get_precondition())
			print("Precondition guaranteed: {}".format(guaranteed))
