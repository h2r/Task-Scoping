import os

this_dir = os.path.dirname(__file__)
problems_path = this_dir + "/problems"

class PickupUnlockOpenPaths:
    domain = this_dir + "/domain.pddl"
    class Problems:
        initial = problems_path + "/initial.pddl"
        door_is_unlocked = problems_path + "/door_is_unlocked.pddl"
