import time
agent_host = None

def begins(s, *args):
    for x in args:
        if len(x) <= len(s) and s[:len(x)] == x:
            return True
    return False

move_sleep = 0.2
plan_path = "examples/malmo/plans/flint.txt"
with open(plan_path,"r") as f:
    pddl_steps = f.read().splitlines()
for s_pddl in pddl_steps:
    action_parts = s_pddl.split("(")[1].split(")")[0].split(" ")
    # Move
    if action_parts[0] == "move-north":
        print("Moving forward")
        agent_host.sendCommand("move 1")
        time.sleep(move_sleep)
    elif action_parts[0] == "move_south":
        print("Moving backwards")
        agent_host.sendCommand("move -1")
        time.sleep(move_sleep)
    elif action_parts[0] == "move_east":
        print("Moving right")
        agent_host.sendCommand("strafe 1")
        time.sleep(move_sleep)
    elif action_parts[0] == "move_west":
        print("Moving left")
        agent_host.sendCommand("strafe -1")
        time.sleep(move_sleep)

    # Hit (we do all destroying at once, so skip)
    elif begins(action_parts[0], "hit"):
        continue

    # Destroy
    # Attack for 10 seconds.
    # If we were destroying multiple types of blocks, we would decide attack time for each block
    if begins(action_parts[0],"destroy"):
        print("Attacking")
        agent_host.sendCommand("attack 1")
        time.sleep(10)
        agent_host.sendCommand("attack 0")
    
    # Pickup happens automatically, so skip
    elif begins(action_parts[0],"pickup"):
        continue