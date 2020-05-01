from hardcoded_1Dtaxi import prepare_1D_taxi
from scoping_disjoint import scope, get_quotient_skills
from hardcoded_taxi2 import prepare_taxi_domain
from utils import condition_str2objects, get_var_names, get_all_objects, get_diff_and_int, str_iter
from hardcoded_blinker import prepare_taxi_domain as prepare_blinker_domain
from hardcoded_domains import make_domain

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

def test_scoping3():
	G, skills_rel, skills_ir, initial_condition, sv_rel, sv_ir = make_domain(causal_link = True, broken_causal_link = True, trivially_relevant = True,
				trivially_irrelevant = True, need_on_and_off = True)
	skills = skills_rel + skills_ir
	sv = sv_rel + sv_ir
	relevant_pvars, relevant_objects, used_skills = scope(G, skills, initial_condition)
	sv_false_ir,  sv_correct_rel, sv_false_rel = get_diff_and_int(str_iter(sv_rel), str_iter(relevant_pvars))
	print("~~~~~Pvars~~~~~")
	print(f"Correctly relevant: {sv_correct_rel}")
	print(f"Falsely irrelevant: {sv_false_ir}")
	print(f"Falsely relevant: {sv_false_rel}")

	print("\n~~~~Skills~~~~")
	skills_false_ir,  skills_correct_rel, skills_false_rel = get_diff_and_int(str_iter(skills_rel), str_iter(used_skills))
	print(f"\nCorrectly Relevant:")
	for s in skills_correct_rel: print(s)
	print(f"\nFalsely irrelevant:")
	for s in skills_false_ir: print(s)
	print(f"\nFalsely relevant:")
	for s in skills_false_rel: print(s)
	#Why does it think (CL,    CL-G,    ('G',)) is relevant? It clearly knows CL is not.

	# print("Relevant skills:")
	# for s in skills_rel: print(s)
	# print("~~~~Results~~~~")
	# print("Relevant Skills:")
	# for s in used_skills: print(s)
	#





if __name__ == "__main__":
	# test_scoping()
	# test_quotient()
	# test_scoping2()
	# test_blinker()
	test_scoping3()