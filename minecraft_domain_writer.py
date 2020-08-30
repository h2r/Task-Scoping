from collections import OrderedDict
from itertools import product

item_types = ["apple", "potato", "rabbit", "diamond-axe", "orchid-flower", "daisy-flower"]
inventory_types = ["apples", "potatoes", "orchids", "daisies", "raw-rabbits", "cooked-rabbits"]
type2name = {
    "apple":"ap",
    "potato":"tot",
    "rabbit":"rab",
    "diamond-axe":"ax",
    "orchid-flower":"orc",
    "daisy-flower":"daisy",
    "bedrock-block":"bed"
}

def set_objects(item_counts):
    s_prefix = "(:objects"
    s_suffix = ")"
    type_lines = []
    type_lines.append("steve - agent")
    for item_type, n in item_counts.items():
        name_prefix = type2name[item_type]
        obj_names = [f"{name_prefix}{i}" for i in range(n)]
        this_line = " ".join(obj_names) + " - " + item_type
        type_lines.append(this_line)
    return s_prefix + "\n\t" + "\n\t".join(type_lines) + "\n" + s_suffix
def get_init_conds_agent():
    init_conds = []
    agent_name = "Steve"
    init_conds.append(f"(= (agent-x {agent_name}) 0)")
    init_conds.append(f"(= (agent-y {agent_name}) 0)")
    init_conds.append(f"(= (agent-z {agent_name}) 0)")
    init_conds.append(f"( agent-has-pickaxe {agent_name} )")
    for item_type in inventory_types:
        init_conds.append(f"(= (agent-num-{item_type} {agent_name}) 0)")
    return init_conds
def get_init_conds_items(item_counts):
    init_conds = []
    y = 1
    for item_type, n in item_counts.items():
        init_conds.append("")
        name_prefix = type2name[item_type]
        for i in range(n):
            init_conds.append("")
            init_conds.append(f"(= ({item_type}-x {name_prefix}{i}) {i})")
            init_conds.append(f"(= ({item_type}-y {name_prefix}{i}) {y})")
            init_conds.append(f"(= ({item_type}-z {name_prefix}{i}) 0)")
            init_conds.append(f"( {item_type}-present {name_prefix}{i} )")
    return init_conds

def get_init_conds_boundary(positions):
    name_prefix = type2name["bedrock-block"]
    init_conds = []
    for i, p in enumerate(positions):
        name = f"{name_prefix}{i}"
        init_conds.append("")
        init_conds.append(f"(= (bl-x {name}) {p[0]})")
        init_conds.append(f"(= (bl-y {name}) {p[1]})")
        init_conds.append(f"(= (bl-z {name}) {p[2]})")
        init_conds.append(f"(block-present {name})")
    return init_conds

def count_boundary_blocks(x,y,z):
    wall_blocks = (x*2 + y*2)*z
    ceiling_and_floor_blocks = x*y*2
    return wall_blocks + ceiling_and_floor_blocks

def get_boundary_positions(x_min, x_max, y_min, y_max, z_min, z_max):
    positions = []
    for x,y in product(range(x_min - 1, x_max + 2), range(y_min - 1, y_max + 2)):
        # Ceiling
        positions.append((x,y,z_max + 1))
        # Floor
        positions.append((x,y,z_min - 1))

    for x, z in product(range(x_min - 1, x_max + 2), range(z_min - 1, z_max + 2)):
        # Front wall
        positions.append((x,y_min - 1,z))
        # Back wall
        positions.append((x, y_max + 1, z))
    for z,y in product(range(z_min - 1, z_max + 2), range(y_min - 1, y_max + 2)):
        # Left wall
        positions.append((x_min - 1, y, z))
        # Right wall
        positions.append((x_max + 1, y, z))
    return positions


header = """(define (problem MINECRAFTCONTRIVED-1)
(:domain minecraft-contrived)"""

goal = """(:goal (and
        (> (agent-num-apples steve) 0)
    )
)

"""
def make_init_conds_str(init_conds):
    s_prefix = "(:init"
    s_suffix = ")"
    return s_prefix + "\n\t" + "\n\t".join(init_conds) + "\n" + s_suffix
x_min, x_max = 0, 2
y_min, y_max = 0, 2
z_min, z_max = 0, 2

item_counts = OrderedDict([("apple",2),("potato",1)])

boundary_positions = get_boundary_positions(x_min, x_max, y_min, y_max, z_min, z_max)
init_conds = get_init_conds_agent() + get_init_conds_items(item_counts)
# init_conds += get_init_conds_boundary(boundary_positions)
init_conds = make_init_conds_str(init_conds)
# item_counts["bedrock-block"] = len(boundary_positions)
object_declaration = set_objects(item_counts)

prob_parts = [header, object_declaration, init_conds, goal, ")"]
prob_s = "\n\n\n".join(prob_parts)

tgt_path = "examples/minecraft/prob-02.pddl"
print(prob_s)
with open(tgt_path, "w") as f:
    f.write(prob_s)
# print(set_objects(item_counts))
# print(set_initial_conditions(item_counts))