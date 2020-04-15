from hardcoded_1Dtaxi import prepare_1D_taxi
from scoping_disjoint import scope, get_quotient_skills
if __name__ == "__main__":
	skills_list, skill_dict, goal, [], solver = prepare_1D_taxi()
	for s in skills_list: s.effect = [str(x) for x in s.effect]
	mn_skills = [s for s in skills_list if s.get_action() == "move_north()"]
	print("Concrete skills:")
	for s in mn_skills: print(s)
	irrelevant_pvars = ["passenger-y-curr(p1)"]
	mn_quotient = get_quotient_skills(mn_skills, denominator=irrelevant_pvars)
	print(f"Ignoring {irrelevant_pvars}:")
	for s in mn_quotient: print(s)