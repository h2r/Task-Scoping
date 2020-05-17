from utils import condition_str2objects, expr2pvar_names_single, get_all_objects, get_diff_and_int, str_iter
from hardcoded_blinker import prepare_taxi_domain as prepare_blinker_domain
from scoping import scope
from hardcoded_domains import make_domain
from skill_classes import merge_skills
import pdb

def test_blinker():
	# Won't work until we fix EffectTypes in hardcoded_blinker.py
	goals, skills, start_condition, pvars = prepare_blinker_domain(n_passegners=2, blinker=True, goal=(3,7))
	# pdb.set_trace()
	relevant_pvars, used_skills = scope(goals, skills, start_condition)
	print("\n~~~All Skills~~~")
	for s in skills: print(str(s) + "\n")
	print("\n~~~Relevant skills~~~")
	for s in used_skills: print(s)
	print("\n~~~All Objects~~~")
	all_objects = get_all_objects(skills)
	for o in all_objects: print(o)
	relevant_objects = []
	for p in relevant_pvars:
		relevant_objects.extend(condition_str2objects(str(p)))
	relevant_objects = sorted(list(set(relevant_objects)))
	print("\n~~~Relevant Objects~~~")
	for o in relevant_objects: print(o)
	print("\n~~~Relevant Pvars~~~")
	for p in relevant_pvars: print(p)



if __name__ == "__main__":
	test_blinker()