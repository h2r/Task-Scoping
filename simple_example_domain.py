import copy
import z3
from classes import *
from scoping import *
from instance_building_utils import *
"""
Simple domain. Press button once lights are on.
"""
types = ["light","button"]
actions = [("turn_on","light"), ("press","button")]
attributes = [
	DomainAttribute('on',z3.Bool,['light']),
	DomainAttribute('pressed',z3.Bool,['button'])
]
object_counts = {"light":2, "button":2}
object_names = object_counts_to_names(object_counts)
#Make str2var dict
str2var = {}
for a in attributes:
	groundings = a.ground(object_names)
	for g in groundings:
		str2var[g] = a.type(g)
g2v = g2v_builder(str2var)
#Get skills
skills = []
#push button skills
lights_on_condition = AndList(*[g2v('on',[i]) for i in range(object_counts['light'])])
for b_id in range(object_counts['button']):
	skills.append(Skill(lights_on_condition, g2n('press', [b_id]), [g2n('pressed', [b_id])]))
#Turn on light skills
for l_id in range(object_counts['light']):
	light_off_condition = (g2v('on',[l_id]) == False)
	skills.append(Skill(light_off_condition, g2n('turn_on', [l_id]), [g2n('on', [l_id])]))
#Set init state
solver_init_lights_off = z3.Solver()
solver_init_lights_on = z3.Solver()
for l_id in range(object_counts["light"]):
	solver_init_lights_off.add(g2v('on',[l_id]) == False)
	solver_init_lights_on.add(g2v('on',[l_id]) == True)
for b_id in range(object_counts['button']):
	solver_init_lights_off.add(g2v('pressed',[b_id]) == False)
	solver_init_lights_on.add(g2v('pressed',[b_id]) == False)

#Set goal
all_buttons_pressed_condition = AndList(*[g2v('pressed',[b_id]) for b_id in range(object_counts['button'])])

#Scope
scoped_init_off, _ = scope(all_buttons_pressed_condition,skills,solver=solver_init_lights_off)
scoped_init_on, _ = scope(all_buttons_pressed_condition,skills,solver=solver_init_lights_on)
print("Scoped init off:")
print(scoped_init_off)
print("Scoped init on:")
print(scoped_init_on)
