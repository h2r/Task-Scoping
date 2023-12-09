import os

this_dir = os.path.dirname(__file__)
problems_path = this_dir + "/problems"

class RadioPaths:
    domain = this_dir + "/domain.pddl"
    class Problems:
        initial = problems_path + "/initial.pddl"
