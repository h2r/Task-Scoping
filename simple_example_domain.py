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
object_counts = {"light":1, "button":1}
#Make str2var dict
str2var = {}
for
#Get skills
skills = []
lights_on_condition =
#Set init state

#Set goal
