import os

this_dir = os.path.dirname(__file__)
problems_path = this_dir + "/problems"

class DoubleDoorsPaths:
    domain = this_dir + "/domain.pddl"
    class Problems:
        outside_left_open_no_key = problems_path + "/outside_left_open_no_key.pddl"
