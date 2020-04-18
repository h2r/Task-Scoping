from hardcoded_1Dtaxi import prepare_1D_taxi
from scoping_disjoint import scope, get_quotient_skills
from hardcoded_taxi2 import prepare_taxi_domain
from utils import condition_str2objects, get_var_names, get_all_objects
from hardcoded_blinker import prepare_taxi_domain as prepare_blinker_domain

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
	print("All Objects")
	all_objects = get_all_objects(skills_list)
	for o in all_objects: print(o)
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
	print("All Objects")
	all_objects = get_all_objects(skills)
	for o in all_objects: print(o)
	print("~~~~~")
	print("~~~Relevant Objects")
	for o in relevant_objects: print(o)

def test_blinker():
	goals, skills, start_condition, pvars = prepare_blinker_domain(n_passegners=2, blinker=True, goal=(None,7))
	for s in skills: s.effect = [str(x) for x in s.effect]
	relevant_pvars, relevant_objects, used_skills = scope(goals, skills, start_condition)
	print("\n~~~All Skills~~~")
	for s in skills: print(str(s) + "\n")
	print("\n~~~Relevant skills~~~")
	for s in used_skills: print(s)
	print("\n~~~All Objects~~~")
	all_objects = get_all_objects(skills)
	for o in all_objects: print(o)
	print("\n~~~Relevant Objects~~~")
	for o in relevant_objects: print(o)
	print("\n~~~Relevant Pvars~~~")
	for p in relevant_pvars: print(p)

if __name__ == "__main__":
	# test_scoping()
	# test_quotient()
	# test_scoping2()
	test_blinker()