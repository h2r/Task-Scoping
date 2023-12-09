"""Helpers to get example domain paths."""
from __future__ import annotations
import os

domains_dir = os.path.dirname(__file__) + "/domains"

class Minecraft3Paths:
    """Just throwing this in a class for static analysis/autocomplete/grouping."""
    dir = domains_dir + "/minecraft3" 
    domain = dir + "/minecraft-contrived3.pddl"
    planks_irrel = dir + "/prob_make_wooden_planks_irrel.pddl"
    planks_rel = dir + "/prob_make_wooden_planks_rel.pddl"
