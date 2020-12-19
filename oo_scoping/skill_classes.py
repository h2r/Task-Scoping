from typing import List, Iterable, Tuple, Hashable, Union
from itertools import chain, product
from collections import OrderedDict
import z3
import copy
from oo_scoping.utils import simplify_disjunction, flatten, get_unique_z3_vars

class EffectType():  #EffectTypes are Immutable
	def __init__(self, pvar: z3.ExprRef, index: int):
		self.pvar, self.index = pvar, index
	def __eq__(self, other):
		return z3.eq(self.pvar, other.pvar) and self.index == other.index
	def __lt__(self, other):
		# TODO incorporate pvar type into sort.
		if str(self.pvar) > str(other.pvar): return False
		if str(self.pvar) == str(other.pvar) and self.index >= other.index: return False
		return True
	def __repr__(self):
		return f"ET({self.pvar},{self.index})"
	def __str__(self):
		return self.__repr__()
	def __hash__(self):
		return hash((hash(self.pvar), hash(self.index)))

class EffectTypePDDL():  #EffectTypes are Immutable
	def __init__(self, pvar: z3.ExprRef, index, params: Iterable= None):
		self.pvar, self.index = pvar, index
		# These params are NOT the same as pddl params, and should probably be renamed
		# These params are vars on which the effect relies - ex. in p.y <- t.y, t.y is a param
		self.params = params if params is not None else tuple()
	def __eq__(self, other):
		return z3.eq(self.pvar, other.pvar) and self.index == other.index and self.params == other.params
	def __lt__(self, other):
		# TODO incorporate pvar type into sort.
		if str(self.pvar) > str(other.pvar): return False
		if str(self.pvar) == str(other.pvar) and str(self.index) >= str(other.index): return False
		if str(self.pvar) == str(other.pvar) and str(self.index) >= str(other.index) and str(self.params) >= str(other.params): return False
		return True
	def __repr__(self):
		# return f"ET({self.pvar},{self.index},{self.params})"
		# I'm tempted to use unicode arrow 
		return f"{self.pvar} <- {self.index}"
	def __str__(self):
		return self.__repr__()
	def __hash__(self):
		return hash((hash(self.pvar), hash(self.index), hash(self.params)))

class SkillPDDL(): #Skills are Immutable
	def __init__(self, precondition: z3.ExprRef, action: Union[str, List[str], Tuple[str]], effects: Union[Iterable[EffectTypePDDL], EffectTypePDDL]
				 , side_effects: Union[Iterable[EffectTypePDDL], EffectTypePDDL] = None):
		if side_effects is None: side_effects = ()
		elif isinstance(side_effects, EffectType): side_effects = (side_effects,)
		if isinstance(effects, EffectType): effects = (effects,)
		# z3 doesn't like vanilla python bools, so we convert those to the z3-equivalent. This makes it so you can
		# pass in True or False as a precondition without ex. Skill.__eq__ throwing an error
		if isinstance(precondition,bool): precondition = z3.BoolVal(precondition)
		self.precondition, self.action = precondition, copy.copy(action) #Copy in case we are passed a list
		if isinstance(effects, EffectTypePDDL): effects = [effects]
		self.effects: Tuple[EffectType] = tuple(sorted(set(effects)))
		self.side_effects: Tuple[EffectType] = tuple(sorted(set(side_effects)))
	@property
	def all_effects(self) -> Tuple[EffectType]:
		return tuple(set(self.effects + self.side_effects))
	def __eq__(self, other):
		if not isinstance(other, Skill): return False
		same_prec = z3.eq(self.precondition,other.precondition)
		same_action = (self.action == other.action)
		same_effects = self.effects == other.effects
		same_side_effets = self.side_effects == other.side_effects
		return  same_prec and same_action and same_effects and same_side_effets
	def __repr__(self):
		s = f"{self.action}\nPrecondition: {self.precondition}\nEffects: {self.effects}" \
			f"\nSide Effects: {self.side_effects}"
		return s
	def __str__(self):
		return self.__repr__()
	def __hash__(self):
		part_hashes = []
		for x in [self.precondition, self.action, self.effects, self.side_effects]:
			part_hashes.append(hash(x))
		return hash(tuple(part_hashes))
	def __lt__(self, other):
		# NOTE: This sort is arbitrary. We are defining it just to get a canonical ordering.
		return str(self) < str(other)
		# if self.action < other.action: return True
		# elif self.action > other.action: return False
	
	def move_irrelevant2side_effects(self, relevant_pvars):
		"""Returns a new skill with irrelevant pvars moved to side effects"""
		# Check that no relevant vars are in side effects
		"""
		TODO side effects should be list of EffectTypes. We can extract pvars from these as needed.
		"""
		# for e in self.side_effects:
		# 	if e.pvar in relevant_pvars:
		# 		raise ValueError(f"Skill has relevant pvar in side effects:\n{self}")

		new_effects = []
		new_side_effects = list(copy.copy(self.side_effects))
		for e in self.effects:
			# if e.pvar in relevant_pvars:
			if(relevant_pvars.get(e.pvar) is not None):
				new_effects.append(e)
			else:
				new_side_effects.append(e)
		return SkillPDDL(self.precondition, self.action, new_effects, new_side_effects)
	@property
	def params(self):
		params = []
		for x in self.effects:
			if hasattr(x, "params"):
				params.extend(x.params)
		return get_unique_z3_vars(params)
		# return tuple(sorted(list(set(params))))
		# return tuple(chain(*[x.params for x in self.effects]))

class Skill(): #Skills are Immutable
	def __init__(self, precondition: z3.ExprRef, action: str, effects: Union[Iterable[EffectType], EffectType]
				 , side_effects: Union[Iterable[EffectType], EffectType] = None):
		if side_effects is None: side_effects = ()
		elif isinstance(side_effects, EffectType): side_effects = (side_effects,)
		if isinstance(effects, EffectType): effects = (effects,)
		# z3 doesn't like vanilla python bools, so we convert those to the z3-equivalent. This makes it so you can
		# pass in True or False as a precondition without ex. Skill.__eq__ throwing an error
		if isinstance(precondition,bool): precondition = z3.BoolVal(precondition)
		self.precondition, self.action = precondition, action
		self.effects: Tuple[EffectType] = tuple(sorted(set(effects)))
		self.side_effects: Tuple[EffectType] = tuple(sorted(set(side_effects)))
	@property
	def all_effects(self) -> Tuple[EffectType]:
		return tuple(set(self.effects + self.side_effects))
	def __eq__(self, other):
		if not isinstance(other, Skill): return False
		same_prec = z3.eq(self.precondition,other.precondition)
		same_action = (self.action == other.action)
		same_effects = self.effects == other.effects
		same_side_effets = self.side_effects == other.side_effects
		return  same_prec and same_action and same_effects and same_side_effets
	def __repr__(self):
		s = f"Precondition: {self.precondition}\nAction: {self.action}\nEffects: {self.effects}" \
			f"\nSide Effects: {self.side_effects}"
		return s
	def __str__(self):
		return self.__repr__()
	def __hash__(self):
		part_hashes = []
		for x in [self.precondition, self.action, self.effects, self.side_effects]:
			part_hashes.append(hash(x))
		return hash(tuple(part_hashes))
	def __lt__(self, other):
		# NOTE: This sort is arbitrary. We are defining it just to get a canonical ordering.
		return str(self) < str(other)
		# if self.action < other.action: return True
		# elif self.action > other.action: return False
	def move_irrelevant2side_effects(self, relevant_pvars):
		"""Returns a new skill with irrelevant pvars moved to side effects"""
		# Check that no relevant vars are in side effects
		for e in self.side_effects:
			if e.pvar in relevant_pvars:
				raise ValueError(f"Skill has relevant pvar in side effects:\n{self}")

		new_effects = []
		new_side_effects = list(copy.copy(self.side_effects))
		for e in self.effects:
			if e.pvar in relevant_pvars:
				new_effects.append(e)
			else:
				new_side_effects.append(e)
		return Skill(self.precondition, self.action, new_effects, new_side_effects)

def merge_skills_pddl(skills: Iterable[SkillPDDL], relevant_pvars: Iterable[z3.ExprRef], solver = None):
	"""
	Merges skills that have the same effects on relevant_pvars
	:param solver: A z3 solver. Use this arg to assume state constraints when simplifying disjunctions
	"""
	new_skills = []
	hashed_skills = OrderedDict()

	rel_pvar_dict = {}
	for rel_pvar in relevant_pvars:
		rel_pvar_dict[rel_pvar] = True

	# Move irrelevant pvars to side effects and group skills by actions and effect types
	for s in skills:
		# s = s.move_irrelevant2side_effects(relevant_pvars)
		s = s.move_irrelevant2side_effects(rel_pvar_dict)
		k = (s.effects)
		if k not in hashed_skills.keys(): hashed_skills[k] = []
		hashed_skills[k].append(s)
	
	print("Done getting skills according to effect")

	# Merge skills that share a key
	for (effects), sks in hashed_skills.items():
		# Skip empty effects
		if len(effects) == 0: continue
		actions = sorted(list(set(flatten([s.action for s in sks]))))
		if 'move-north' in actions:
			print("north time")
		side_effects = chain(*[s.side_effects for s in sks])
		conds = [s.precondition for s in sks]
		precondition = simplify_disjunction(conds, my_solver=solver)
		# Actions is the list of actions that appeared in any of the parent skills
		if len(actions) == 1: actions = actions[0]
		s_merged = SkillPDDL(precondition, actions, effects, side_effects)
		new_skills.append(s_merged)
	
	print("Done Quotienting!")

	return sorted(new_skills)

def merge_skills(skills: Iterable[Skill], relevant_pvars: Iterable[z3.ExprRef]):
	new_skills = []
	hashed_skills = OrderedDict()
	# Move irrelevant pvars to side effects and group skills by actions and effect types
	for s in skills:
		s = s.move_irrelevant2side_effects(relevant_pvars)
		k = (s.action, s.effects)
		if k not in hashed_skills.keys(): hashed_skills[k] = []
		hashed_skills[k].append(s)
	# Merge skills that share a key
	for (action, effects), sks in hashed_skills.items():
		# Skip empty effects
		if len(effects) == 0: continue
		side_effects = chain(*[s.side_effects for s in sks])
		precondition = simplify_disjunction([s.precondition for s in sks])
		new_skills.append(Skill(precondition, action, effects, side_effects))
	return sorted(new_skills)


def test_effect_type_eq():
	pvar0 = z3.Bool("b0")
	pvar1 = z3.Bool("b1")
	pvar2 = z3.Int("i0")
	et0 = EffectType(pvar0, 0)
	et0_1 = EffectType(pvar0,0)
	print((et0 == et0_1) == True)
	et1 = EffectType(pvar1, 0)
	print((et0 == et1) == False)
	et2 = EffectType(pvar2,0)
	print((et2 != et0))

def test_effect_type_hash():
	pvar0 = z3.Bool("b0")
	pvar1 = z3.Bool("b1")
	pvar2 = z3.Int("i0")
	et0 = EffectType(pvar0, 0)
	et0_1 = EffectType(pvar0,0)
	et1 = EffectType(pvar1, 0)
	et2 = EffectType(pvar2,0)
	s = list(set([et0,et0_1,et1,et2]))
	print(s)
def test_skill_eq():
	pvars = [z3.Bool(f"b{i}") for i in range(2)]
	ets = OrderedDict()
	for p_id, i in product(range(len(pvars)), [0,1]):
		p = pvars[p_id]
		ets[(p_id,i)] = EffectType(p,i)
	# ets = [EffectType(p,0) for p in pvars]
	s0 = Skill(True, "action", [ets[(0,0)]])
	s0_copy = Skill(True, "action", [ets[(0,0)]])
	print(s0==s0_copy)
	s1 = Skill(pvars[1], "action", [ets[(0,0)]])
	print(s0 != s1)

def test_merge_skills():
	# TODO this is a bad example bc preconditions are not disjoint.
	pvars = [z3.Bool(f"b{i}") for i in range(2)]
	ets = OrderedDict()
	for p_id, i in product(range(len(pvars)), [0,1]):
		p = pvars[p_id]
		ets[(p_id,i)] = EffectType(p,i)

	# ets = [EffectType(p,0) for p in pvars]
	# sboth = Skill(pvars[0], "action_both", ets)
	s0 = Skill(pvars[0], "action", [ets[(0,0)], ets[(1,0)]])
	s1 = Skill(z3.Not(pvars[0]), "action", [ets[(0,0)]])
	s2 = Skill(pvars[1], "action", [ets[(0,1)]])
	# s2 =
	# merged = merge_skills([s0,s1, s2], [pvars[0]])
	merged = merge_skills_pddl([s0,s1, s2], [pvars[0]])

	for m in merged:
		print(m)
		print("")
	merged_correct = sorted([Skill(True, "action", [ets[(0,0)]], [ets[(1,0)]]), s2])
	print(f"\nCorrect: {merged_correct == merged}")


if __name__ == "__main__":
	test_merge_skills()
	# test_effect_type_eq()
	# test_skill_eq()
	# test_effect_type_hash()