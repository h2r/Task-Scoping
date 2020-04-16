from hardcoded_1Dtaxi import prepare_1D_taxi
from scoping_disjoint import scope, get_quotient_skills

def test_quotient():
	skills_list, skill_dict, goal, _, solver = prepare_1D_taxi()
	for s in skills_list: s.effect = [str(x) for x in s.effect]
	mn_skills = [s for s in skills_list if s.get_action() == "move_north()"]
	print("Concrete skills:")
	for s in mn_skills: print(s)
	irrelevant_pvars = ["passenger-y-curr(p1)"]
	mn_quotient = get_quotient_skills(mn_skills, denominator=irrelevant_pvars)
	print(f"Ignoring {irrelevant_pvars}:")
	print()
	print("Changed Skills")
	for s in mn_quotient: print(s)

def test_scoping():
	skills_list, _, goal, _, solver = prepare_1D_taxi()
	for s in skills_list: s.effect = [str(x) for x in s.effect]
	relevant_objects, used_skills = scope(goal, skills_list, start_condition=None, solver=solver)
	print("~~~~~")
	print("Relevant objects")
	for o in relevant_objects: print(o)
	print("Relevant skills")
	for s in used_skills: print(s)

if __name__ == "__main__":
	test_scoping()