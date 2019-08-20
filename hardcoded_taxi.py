import copy
import z3
from classes import *
from scoping import *
#TODO add asserts
def object_counts_to_names(object_counts):
	object_names = {}
	for k,v in object_counts.items():
		object_names[k] = [str(i) for i in range(v)]
	return object_names

if __name__ == "__main__":
	types = ['taxi', 'passenger', 'wall']
	actions = [("move_north",'taxi'),("move_south",'taxi'),("move_east",'taxi'),("move_west",'taxi'), ("pickup","taxi","passenger"),("dropoff","taxi","passenger")]
	#Constants
	non_fluents = ['WALL_X', 'WALL_Y','PASSENGER_GOAL_X','PASSENGER_GOAL_Y']
	attributes = [
					DomainAttribute('taxi-x',z3.Int, ['taxi'],["0 < this", "this < 10"]),
		            DomainAttribute('taxi-y',z3.Int, ['taxi'], ["0 < this", "this < 10"]),
		            DomainAttribute('passenger-x-curr',z3.Int,['passenger'], ["0 < this", "this < 10"]),
		            DomainAttribute('passenger-y-curr',z3.Int,['passenger'], ["0 < this", "this < 10"]),
					DomainAttribute('passenger-in-taxi',z3.Bool,['passenger','taxi'])
	]
	taxi_x, taxi_y, passenger_x_curr, passenger_y_curr, passenger_in_taxi = attributes
	object_counts = {
		"passenger":2,
		"taxi":1,
		"wall":0
	}
	#z3 stuff
	#Define propositions
	all_object_names = object_counts_to_names(object_counts)
	name_to_z3_var = {}

	for att in attributes:
		grounded_attributes = att.ground(all_object_names)
		for g in grounded_attributes:
			#Define var
			name_to_z3_var[g] = att.type(g)
			#Apply constraints
			pass
	solver = z3.Solver()
	#Define init state
	passengers_in_taxi_var_names = passenger_in_taxi.ground(all_object_names)
	for p in passengers_in_taxi_var_names:
		p_in_t_att = name_to_z3_var[p]
		solver.add(p_in_t_att == False)
	# solver.push()
	#Make skill triples
	skill_triples = []

	#Movement without passenger
	#Empty taxi condition
	object_names = {
		"passenger": [str(i) for i in range(object_counts["passenger"])]
	}
	for t in range(object_counts['taxi']):
		object_names["taxi"] = [str(t)]
		#Empty taxi condition
		passengers_in_taxi_var_names = passenger_in_taxi.ground(object_names)
		# for p in passengers_in_taxi_var_names: print(p)
		taxi_empty_vars = [z3.Not(name_to_z3_var[x]) for x in passengers_in_taxi_var_names]
		taxi_empty_condition = z3.And(*taxi_empty_vars)
		#No wall condition
		pass
		skill_triples.append(SkillTriplet(taxi_empty_condition, "move_north_{}".format(t), ['taxi-y_{}'.format(t)]))
		skill_triples.append(SkillTriplet(taxi_empty_condition, "move_south_{}".format(t), ['taxi-y_{}'.format(t)]))
		skill_triples.append(SkillTriplet(taxi_empty_condition, "move_east_{}".format(t), ['taxi-x_{}'.format(t)]))
		skill_triples.append(SkillTriplet(taxi_empty_condition, "move_west_{}".format(t), ['taxi-x_{}'.format(t)]))

		#Passenger in taxi
		for p_id in range(len(passengers_in_taxi_var_names)):
			passenger_in_taxi_conditions = []
			for p_id2 in range(len(passengers_in_taxi_var_names)):
				p_inTaxi_name = passengers_in_taxi_var_names[p_id2]
				if p_id2 == p_id:
					passenger_in_taxi_conditions.append(name_to_z3_var[p_inTaxi_name])
				else:
					passenger_in_taxi_conditions.append(z3.Not(name_to_z3_var[p_inTaxi_name]))
			taxi_occupance_condition = z3.And(*passenger_in_taxi_conditions)
			skill_triples.append(SkillTriplet(taxi_occupance_condition, "move_north_{}".format(t), ['taxi-y_{}'.format(t), 'passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(taxi_occupance_condition, "move_south_{}".format(t), ['taxi-y_{}'.format(t),'passenger-x-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(taxi_occupance_condition, "move_east_{}".format(t), ['taxi-x_{}'.format(t),'passenger-y-curr_{}'.format(p_id)]))
			skill_triples.append(SkillTriplet(taxi_occupance_condition, "move_west_{}".format(t), ['taxi-x_{}'.format(t),'passenger-y-curr_{}'.format(p_id)]))

		#Test whether start state implies skills
		for skill in skill_triples:
			print("Action: {}".format(skill.get_action()))
			print("Affected variables: {}".format(skill.get_affected_variables()))
			guaranteed = solver_implies_condition(solver, skill.get_precondition())
			print("Precondition guaranteed: {}".format(guaranteed))
