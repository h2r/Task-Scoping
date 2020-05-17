from utils import condition_str2objects, expr2pvar_names_single, get_all_objects, get_diff_and_int, str_iter
from hardcoded_blinker import prepare_taxi_domain as prepare_blinker_domain
from hardcoded_domains import make_domain
from skill_classes import merge_skills
import pdb

def test_blinker():
	goals, skills, start_condition, pvars = prepare_blinker_domain(n_passegners=2, blinker=True, goal=(None,7))
	# pdb.set_trace()
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
	print(f"Initial Condition: {initial_condition}")
	print(f"Goal: {G}")
	skills = skills_rel + skills_ir
	sv = sv_rel + sv_ir
	scoper = Scoper(G, skills, initial_condition)
	relevant_pvars, relevant_objects, used_skills = scoper.scope()
	# relevant_pvars, relevant_objects, used_skills = scope(G, skills, initial_condition)
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




if __name__ == "__main__":
	# test_scoping()
	# test_quotient()
	# test_scoping2()
	# test_blinker()
	test_scoping3()