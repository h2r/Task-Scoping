from hardcoded_1Dtaxi import prepare_1D_taxi
from scoping_disjoint import scope, get_quotient_skills
from hardcoded_taxi2 import prepare_taxi_domain

def test_quotient():
	skills_list, skill_dict, goal, _, solver = prepare_1D_taxi()
	for s in skills_list: s.effect = [str(x) for x in s.effect]
	mn_skills = [s for s in skills_list if s.get_action() == "move_north()"]
	print("Concrete skills:")
	for s in mn_skills: print(s)
	irrelevant_pvars = ["passenger-y-curr(p1)"]
	mn_quotient = get_quotient_skills(mn_skills, denominator=irrelevant_pvars)
	# print(f"\nIgnoring {irrelevant_pvars}:\n")
	print(f"\nSkills modulo effects on {irrelevant_pvars}:\n")
	for s in mn_quotient: print(s)

def test_scoping():
	skills_list, _, goal, _, solver = prepare_1D_taxi()
	for s in skills_list: s.effect = [str(x) for x in s.effect]
	relevant_pvars, relevant_objects, used_skills = scope(goal, skills_list, start_condition=None, solver=solver)
	print("~~~~~")
	print("Relevant objects")
	for o in relevant_objects: print(o)
	print("Relevant skills")
	for s in used_skills: print(s)

def test_scoping2():
	goals, skills, start_condition, pvars = prepare_taxi_domain()
	for s in skills: s.effect = [str(x) for x in s.effect]
	relevant_pvars, relevant_objects, used_skills = scope(goals, skills, start_condition)
	print("~~~All Skills~~~")
	for s in skills: print(s)
	print("~~~Relevant skills~~~")
	for s in used_skills: print(s)
	print("~~~Relevant Objects")
	for o in relevant_objects: print(o)

if __name__ == "__main__":
	# test_scoping()
	# test_quotient()
	test_scoping2()