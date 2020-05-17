from itertools import chain
from typing import Iterable, Union
import z3
from skill_classes import merge_skills, Skill, EffectType
from utils import split_conj, get_atoms, solver_implies_condition


def scope(goals: Union[Iterable[z3.ExprRef], z3.ExprRef], skills: Iterable[Skill]
		  , start_condition: Union[Iterable[z3.ExprRef], z3.ExprRef]):
	if isinstance(goals, z3.ExprRef): goals = split_conj(goals)
	if isinstance(start_condition, z3.ExprRef):	start_condition = split_conj(start_condition)
	solver = z3.Solver()
	solver.push()
	# We make a dummy goal and dummy final skill a la LCP because it simplifies the beginning of the algorithm.
	# We will remove the dummy goal and skill before returning the final results
	dummy_goal = z3.Bool("dummy_goal") #TODO make sure this var does not already exist
	# dummy_goal = z3.And(*goals)
	dummy_final_skill = Skill(z3.And(*goals), "DummyFinalSkill",EffectType(dummy_goal,0))
	pvars_rel = [dummy_goal]
	converged = False
	while not converged:
		skills_rel = merge_skills(skills, pvars_rel)

		all_effects = sorted(list(set(chain([s.all_effects for s in skills]))))
		all_effected_pvars = sorted(list(set(chain([x.pvar for x in all_effects]))))

		causal_links = []
		for c in start_condition:
			threatened_pvars = [x for x in get_atoms(c) if x in all_effected_pvars]
			if len(threatened_pvars) == 0: causal_links.append(c)
		for c in causal_links: solver.push(c)

		pvars_rel_new = []
		for s in skills_rel:
			for prec in split_conj(s.precondition):
				if not solver_implies_condition(solver, prec):
					pvars_rel_new.extend(get_atoms(prec))
		pvars_rel_new = sorted(list(set(pvars_rel_new)))

		if pvars_rel_new == pvars_rel:
			converged = True

		pvars_rel = pvars_rel_new
	pvars_rel.remove(dummy_goal)
	skills_rel.remove(dummy_final_skill)
	return pvars_rel, skills_rel