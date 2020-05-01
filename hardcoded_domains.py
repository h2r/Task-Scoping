import z3
from classes import *
import pdb
from typing import List
from typing import NamedTuple

def make_domain(causal_link = True, broken_causal_link = True, trivially_relevant = True,
				trivially_irrelevant = True, need_on_and_off = True):
	skills_rel = []
	skills_ir = []
	sv_ir = [] #Irrelevant state vars
	sv_rel = [] #Relevant state vars
	initial_condition = []
	G = z3.Bool('G')
	sv_rel.append(G)
	if causal_link:
		CL = z3.Bool('CL') #causal link. Irrelevant
		CL1 = z3.Bool('CL1') #Affects causal link. Irrelevant.
		sv_ir.extend([CL,CL1])
		skills_rel.append(Skill(CL, 'CL-G', [G]))
		skills_ir.append(Skill(CL1, "CL1-CL", [CL]))
		initial_condition.append(CL)
	if broken_causal_link:
		BCL = z3.Bool('BCL')  #Broken causal link. Relevant.
		BCL1 = z3.Bool('BCL1') #Affects bcl. Relevant
		sv_rel.extend([BCL, BCL1])
		initial_condition.append(BCL)
		skills_rel.append(Skill(BCL, 'BCL-G', [G]))
		skills_rel.append(Skill(BCL1, "BCL1-BCL", [BCL]))
	if trivially_relevant:
		R = z3.Bool('R') #Affects g. Relevant
		R1 = z3.Bool('R1') #Affects r. Relevant
		sv_rel.extend([R,R1])
		skills_rel.append(Skill(R, "R-G", [G]))
		skills_rel.append(Skill(R1, "R1-R", [R]))
		skills_rel.append(Skill(R1, "R1-BCL", [BCL]))
	if need_on_and_off:
		B = z3.Bool('B') #Affects r when True, r1 when false. Relevant.
		sv_rel.append(B)
		skills_rel.append(Skill(B, "B-R", [R]))
		skills_rel.append(Skill(z3.Not(B), "(~B)-R1", [R1]))
		initial_condition.append(B)
	if trivially_relevant:
		IR = z3.Bool('IR')  # Trivially irrelevant
		sv_ir.append(IR)
	sv = sv_rel + sv_ir
	skills = skills_rel + skills_ir
	# I forgot the effects should be strings, not vars :/. Also tupleize effects so skills can use __eq__
	for s in skills: s.effect = tuple([str(x) for x in s.effect])
	for s in skills: s.implicit_effects_processed = True
	initial_condition = z3.And(*initial_condition)
	return G, skills_rel, skills_ir, initial_condition, sv_rel, sv_ir

