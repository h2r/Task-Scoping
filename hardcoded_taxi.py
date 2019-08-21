import copy
import z3
from classes import *
from scoping import *


# TODO add asserts
# TODO rewrite so that [north, south, east, west] always come in same order to reduce chance of bugs. NSEW seams best, since it groups x,y
# TODO finish refactoring to use ground2var
def object_counts_to_names(object_counts):
	object_names = {}
	for k, v in object_counts.items():
		object_names[k] = [str(i) for i in range(v)]
	return object_names



if __name__ == "__main__":
	types = ['taxi', 'passenger', 'wall']
	actions = [("move_north", 'taxi'), ("move_south", 'taxi'), ("move_east", 'taxi'), ("move_west", 'taxi'),
			   ("pickup", "taxi", "passenger"), ("dropoff", "taxi", "passenger")]
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
	attribute_to_grounded_names = {}
	constant_to_grounded_names = {}
	name_to_z3_var = {}

	for att in attributes:
		grounded_attributes = att.ground(all_object_names)
		attribute_to_grounded_names[att.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = att.type(g)
			# Apply constraints
			pass
	for c in constants:
		grounded_attributes = c.ground(all_object_names)
		constant_to_grounded_names[c.name] = grounded_attributes
		for g in grounded_attributes:
			# Define var
			name_to_z3_var[g] = c.type(g)
			# Apply constraints
			pass
	def ground2name(att_name, object_ids):
		name = att_name + "_" +  "_".join([str(i) for i in object_ids])
		return name
	def ground2var(att_name, object_ids,var_dict = name_to_z3_var):
		return var_dict[ground2name(att_name,object_ids)]
	solver = z3.Solver()
	# Assign constants and init state
	passengers_you_care_for_value_list = [True] + [False for _ in range(object_counts['passenger'] - 1)]
	passenger_goal_x_values = [2,3]
	passenger_goal_y_values = [3,2]
	passenger_start_x_values = [1,0]
	passenger_start_y_values = [0,1]
	for p_id in range(object_counts['passenger']):
		solver.add(ground2var('PASSENGERS_YOU_CARE_FOR',[p_id]) == passengers_you_care_for_value_list[p_id])
		solver.add(ground2var("PASSENGER_GOAL_X", [p_id]) == passenger_goal_x_values[p_id])
		solver.add(ground2var("PASSENGER_GOAL_Y", [p_id]) == passenger_goal_y_values[p_id])
		solver.add(ground2var("passenger-x-curr",[p_id]) == passenger_start_x_values[p_id])
		solver.add(ground2var("passenger-y-curr",[p_id]) == passenger_start_y_values[p_id])
		for t_id in range(object_counts['taxi']):
			solver.add(ground2var('passenger-in-taxi',[p_id,t_id]) == False)
	assert solver.check() == z3.sat
	# print(solver.assertions())
	solver.push()
	# Make skill triples
	skill_triples = []

	# Movement without passenger
	# Empty taxi Precondition
	object_names = {
		"passenger": [str(i) for i in range(object_counts["passenger"])]
	}
	for t_id in range(object_counts['taxi']):
		object_names["taxi"] = [str(t_id)]
		# Empty taxi Precondition
		passengers_in_taxi_var_names = passenger_in_taxi.ground(object_names)
		# for p in passengers_in_taxi_var_names: print(p)
		taxi_empty_vars = [z3.Not(name_to_z3_var[x]) for x in passengers_in_taxi_var_names]
		taxi_empty_condition = AndList(*taxi_empty_vars)
		# Create not-touching wall conditions
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
			same_x = (ground2var('taxi-x',[t_id]) == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			east_x = (ground2var('taxi-x',[t_id]) + 1 == name_to_z3_var[w_x])
			# noinspection PyTypeChecker
			west_x = (ground2var('taxi-x',[t_id])- 1 == name_to_z3_var[w_x])
			same_y = (ground2var('taxi-y',[t_id]) == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			north_y = (ground2var('taxi-y',[t_id]) + 1 == name_to_z3_var[w_y])
			# noinspection PyTypeChecker
			south_y = (ground2var('taxi-y',[t_id]) - 1 == name_to_z3_var[w_y])

			wall_touch_north_list.append(z3.And(same_x, north_y))
			wall_touch_east_list.append(z3.And(east_x, same_y))
			wall_touch_south_list.append(z3.And(same_x, south_y))
			wall_touch_west_list.append(z3.And(west_x, same_y))
		# Combine touch conditions from each wall to get overall touch conditions
		no_touch_north_condition = z3.Not(z3.Or(*wall_touch_north_list))
		no_touch_east_condition = z3.Not(z3.Or(*wall_touch_east_list))
		no_touch_south_condition = z3.Not(z3.Or(*wall_touch_south_list))
		no_touch_west_condition = z3.Not(z3.Or(*wall_touch_west_list))
		# Add skills for each movement direction
		skill_triples.append(
			SkillTriplet(no_touch_north_condition, "move_north_{}".format(t_id), ['taxi-y_{}'.format(t_id)]))
		skill_triples.append(
			SkillTriplet(no_touch_south_condition, "move_south_{}".format(t_id), ['taxi-y_{}'.format(t_id)]))
		skill_triples.append(
			SkillTriplet(no_touch_east_condition, "move_east_{}".format(t_id), ['taxi-x_{}'.format(t_id)]))
		skill_triples.append(
			SkillTriplet(no_touch_west_condition, "move_west_{}".format(t_id), ['taxi-x_{}'.format(t_id)]))

		# Create single-passenger-in-taxi conditions, and pickup/dropoff
		for p_id in range(len(passengers_in_taxi_var_names)):
			passenger_in_taxi_conditions = []
			for p_id2 in range(len(passengers_in_taxi_var_names)):
				p_inTaxi_name = passengers_in_taxi_var_names[p_id2]
				if p_id2 == p_id:
					passenger_in_taxi_conditions.append(name_to_z3_var[p_inTaxi_name])
				#We don't need to mention the other passengers, but it doesn't hurt. Consider rewriting this bit.
				else:
					passenger_in_taxi_conditions.append(z3.Not(name_to_z3_var[p_inTaxi_name]))
			# taxi_occupance_condition = AndList(*passenger_in_taxi_conditions)
			taxi_occupance_condition = ground2var('passenger-in-taxi',[p_id,0])
			#  Combine passenger in taxi Precondition with no_touch conditions
			move_north_with_passenger_condition = AndList(no_touch_north_condition, taxi_occupance_condition)
			move_east_with_passenger_condition = AndList(no_touch_east_condition, taxi_occupance_condition)
			move_south_with_passenger_condition = AndList(no_touch_south_condition, taxi_occupance_condition)
			move_west_with_passenger_condition = AndList(no_touch_west_condition, taxi_occupance_condition)

			skill_triples.append(SkillTriplet(move_north_with_passenger_condition, "move_north_{}".format(t_id),
											  ['passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_south_with_passenger_condition, "move_south_{}".format(t_id),
											  ['passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_east_with_passenger_condition, "move_east_{}".format(t_id),
											  ['passenger-y-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(move_west_with_passenger_condition, "move_west_{}".format(t_id),
											  ['passenger-y-curr_{}'.format(p_id)]))

			# Add pickup actions
			shared_x_condition = (ground2var('taxi-x',[t_id]) == ground2var('passenger-x-curr',[p_id]))
			shared_y_condition = (ground2var('taxi-y',[t_id]) == ground2var('passenger-y-curr',[p_id]))
			pickup_condition = AndList(shared_x_condition,shared_y_condition,taxi_empty_condition)
			dropoff_condition = name_to_z3_var[passengers_in_taxi_var_names[p_id]]
			skill_triples.append(SkillTriplet(pickup_condition,'pickup_{}_{}'.format(t_id,p_id),[passengers_in_taxi_var_names[p_id]]))
			skill_triples.append(SkillTriplet(dropoff_condition,"dropoff_{}_{}".format(t_id,p_id),passengers_in_taxi_var_names[p_id]))

	# Create goal Precondition. For now, we are using explicit goal Precondition rather than a more general reward
	at_goal_or_unimportant_conditions = []
	for p_id in range(object_counts['passenger']):
		cur_x_var = ground2var('passenger-x-curr',[p_id])
		cur_y_var = ground2var('passenger-y-curr',[p_id])
		goal_x_var = ground2var('PASSENGER_GOAL_X',[p_id])
		goal_y_var = ground2var('PASSENGER_GOAL_Y',[p_id])
		at_goal_condition = ((cur_x_var == goal_x_var) and (cur_y_var == goal_y_var))
		at_goal_or_unimportant_conditions.append(z3.Or(at_goal_condition,z3.Not(ground2var('PASSENGERS_YOU_CARE_FOR',[p_id]))))
	# Since this condition includes each passenger's location in an OR, the scoper thinks they are relevant
	# We can fix this by plugging in constants to expressions and simplifying, but for now I will define an easier goal
	goal_condition_hard_to_parse = AndList(*at_goal_or_unimportant_conditions)
	cared_for_goal_conditions = []
	#Checking this assertion in the loop raises an s
	assert solver.check() == z3.z3.sat

	for p_id in range(object_counts['passenger']):
		result = solver.check()
		assert result == z3.z3.sat, result

		#Check whether we care for the passenger
		solver.push()
		# If the passenger cannot not be cared for, they are cared for
		solver.add(ground2var('PASSENGERS_YOU_CARE_FOR',[p_id]) == False)
		result = solver.check()
		solver.pop()
		if result == z3.z3.unsat:
			cur_x_var = ground2var('passenger-x-curr', [p_id])
			cur_y_var = ground2var('passenger-y-curr', [p_id])
			goal_x_var = ground2var('PASSENGER_GOAL_X', [p_id])
			goal_y_var = ground2var('PASSENGER_GOAL_Y', [p_id])
			at_goal_condition = ((cur_x_var == goal_x_var) and (cur_y_var == goal_y_var))
			cared_for_goal_conditions.append(at_goal_condition)
	goal_condition_easy_to_parse = AndList(cared_for_goal_conditions)

	# goal_condition = Precondition()
	# Test whether start state implies skills
	# for skill in skill_triples:
	# 	pass
		# print("Action: {}".format(skill.get_action()))
		# print("Affected variables: {}".format(skill.get_affected_variables()))
		# guaranteed = solver_implies_condition(solver, skill.get_precondition())
		# print("Precondition guaranteed: {}".format(guaranteed))
	# x = z3.z3util.get_vars(goal_z3)
	# y = x[0]
	# print(x)
	# print(y)

#Run scoping
	print("Scoping")
	discovered_not_guarantees, used_skills = scope(goal_condition_easy_to_parse,skill_triples,solver=solver)
	print(discovered_not_guarantees)