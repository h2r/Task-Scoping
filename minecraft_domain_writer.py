from collections import OrderedDict
from itertools import product

item_types = ["iron","wool","diamond", "stick", "diamond-pickaxe", "apple", "potato"
    , "rabbit", "diamond-axe", "orchid-flower", "daisy-flower", "shears"]
type2name = {
    "apple":"ap",
    "potato":"tot",
    "rabbit":"rab",
    "diamond-axe":"ax",
    "orchid-flower":"orc",
    "daisy-flower":"daisy",
    "bedrock-block":"bed"
}

# def set_objects(item_counts):
#     s_prefix = "(:objects"
#     s_suffix = ")"
#     type_lines = []
#     type_lines.append("steve - agent")
#     for item_type, n in item_counts.items():
#         name_prefix = type2name[item_type]
#         obj_names = [f"{name_prefix}{i}" for i in range(n)]
#         this_line = " ".join(obj_names) + " - " + item_type
#         type_lines.append(this_line)
#     return s_prefix + "\n\t" + "\n\t".join(type_lines) + "\n" + s_suffix

def get_object_declarations(objects):
    prefix = "(:objects\n\t"
    suffix = "\n)"
    lines = []
    for type_name, object_names in objects.items():
        lines.append( " ".join(object_names) + " - " + type_name)
    return prefix + "\n\t".join(lines) + suffix



def get_init_location_conds(pos, object_name):
    x,y,z = pos
    init_conds = []
    init_conds.append(f"(= (x {object_name}) {x})")
    init_conds.append(f"(= (y {object_name}) {y})")
    init_conds.append(f"(= (z {object_name}) {z})")
    return init_conds


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

def make_init_conds_str(init_conds):
    s_prefix = "(:init"
    s_suffix = ")"
    return s_prefix + "\n\t" + "\n\t".join(init_conds) + "\n" + s_suffix


def get_inventory_funcs(item_types):
    inventory_count_vars = []
    for t in item_types:
        inventory_count_vars.append(f"( agent-num-{t} ?ag - agent )")
    return inventory_count_vars
    
def get_pickup_actions(item_types):
    pass

def invert_dict(d):
    d_new = OrderedDict()
    for k, v in d.items():
        if v not in d_new.keys():
            d_new[v] = []
        d_new[v].append(k)
    return d_new

def get_functions_str(functions):
    prefix = "(:functions"
    suffix = ")"
    lines = ["\t" + f for f in functions]
    body = "\n".join(lines)
    return prefix + '\n' + body + "\n" + suffix

def get_predicates_str(predicates):
    prefix = "(:predicates"
    suffix = ")"
    lines = ["\t " + f for f in predicates]
    body = "\n".join(lines)
    return prefix + '\n' + body + "\n" + suffix
def get_move_actions():
    s = "(:action move-north\n :parameters (?ag - agent)\n :precondition (and (agent-alive ?ag)\n                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))\n                                                    (= (y ?bl) (+ (y ?ag) 1))\n                                                    (= (z ?bl) (+ (z ?ag) 1))))))\n :effect (and (increase (y ?ag) 1))\n)\n\n(:action move-south\n :parameters (?ag - agent)\n :precondition (and (agent-alive ?ag)\n                    (not (exists (?bl - block) (and (= (x ?bl) (x ?ag))\n                                                    (= (y ?bl) (- (y ?ag) 1))\n                                                    (= (z ?bl) (+ (z ?ag) 1))))))\n :effect (and (decrease (y ?ag) 1))\n)\n\n(:action move-east\n :parameters (?ag - agent)\n :precondition (and (agent-alive ?ag)\n                    (not (exists (?bl - block) (and (= (x ?bl) (+ (x ?ag) 1))\n                                                    (= (y ?bl) (y ?ag))\n                                                    (= (z ?bl) (+ (z ?ag) 1))))))\n :effect (and (increase (x ?ag) 1))\n)\n\n(:action move-west\n :parameters (?ag - agent)\n :precondition (and (agent-alive ?ag)\n                    (not (exists (?bl - block) (and (= (x ?bl) (- (x ?ag) 1))\n                                                    (= (y ?bl) (y ?ag))\n                                                    (= (z ?bl) (+ (z ?ag) 1))))))\n :effect (and (decrease (x ?ag) 1))\n)"
    return s
def make_pickup_actions(item_types):
    action_template = """(:action pickup-{t}
 :parameters (?ag - agent ?i - {t})
 :precondition (and (present ?i)
                    (= (x ?i) (x ?ag))
                    (= (y ?i) (y ?ag))
                    (= (z ?i) (z ?ag)))
 :effect (and (increase (agent-num-{t} ?ag) 1)
              (not (present ?i)))
)
"""
    actions = []
    for t in item_types:
        actions.append(action_template.format(t=t))
    return actions

def get_destructible_block_action(block_type, needed_tool = None):
    # TODO either set x,y,z to far away, or check for block existence in movement actions
    if needed_tool is None:
        tool_precond = ""
    else:
        tool_precond = f"\n                        ( >= ( agent-num-{needed_tool} ?ag ) 1 )"
    hit_s = f"""(:action hit-{block_type}
    :parameters (?ag - agent ?b - {block_type})
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (< (block-hits ?b) 4){tool_precond})
    :effect (and (increase (block-hits ?b) 1))
    )"""
    destroy_s = f"""(:action destroy-{block_type}
    :parameters (?ag - agent ?b - {block_type})
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (z ?ag))
                        (block-present ?b)
                        (= (block-hits ?b) 3){tool_precond})
    :effect (not (block-present ?b))
    )"""
    return [hit_s, destroy_s]

def make_domain():
    sections = []
    header = "(define (domain minecraft-contrived)\n(:requirements :typing :fluents :negative-preconditions :universal-preconditions :existential-preconditions)"
    footer = ")"
    sections.append(header)
    type_hierarchy = OrderedDict()
    # locatables have position
    # items have agent count and present, in addition to location
    type_hierarchy["locatable"] = None
    type_hierarchy["agent"] = "locatable"
    type_hierarchy["item"] = "locatable"
    type_hierarchy["block"] = "locatable"
    type_hierarchy["bedrock"] = "block"
    type_hierarchy["destructible-block"] = "block"
    type_hierarchy["obsidian-block"] = "destructible-block"
    # item_types_irrelevant = ["apple", "potato", "rabbit", "diamond-axe", "orchid-flower", "daisy-flower"]
    # item_types = ["diamond", "stick", "iron", "diamond-pickaxe", "shears", "wool"]
    for i in item_types:
        type_hierarchy[i] = "item"
    inverse_type_hierarchy = invert_dict(type_hierarchy)
    types_s = make_types_declaration(type_hierarchy)
    sections.append(types_s)
    
    predicates = []
    predicates.append("( present ?i - item )")  
    predicates.append("( block-present ?b - block )")
    predicates.append("( agent-alive ?ag - agent )")
    functions = []
    functions.append("( block-hits ?b - destructible-block )")
    functions.extend(get_inventory_funcs(inverse_type_hierarchy["item"]))
    for d in ["x","y","z"]:
        functions.append(f"( {d} ?l - locatable )")

    predicates_s = get_predicates_str(predicates)
    sections.append(predicates_s)
    functions_s = get_functions_str(functions)
    sections.append(functions_s)

    actions = []
    actions.append(get_move_actions())
    actions.extend(make_pickup_actions(inverse_type_hierarchy["item"]))

    diamond_pick_inputs = OrderedDict([("stick",2),("diamond",3)])
    diamond_pick_outputs = OrderedDict([("diamond-pickaxe",1)])
    craft_diamond_pickaxe = get_crafting_action("craft-diamond-pickaxe", diamond_pick_inputs, diamond_pick_outputs)

    shears_inputs = OrderedDict([("iron",2)])
    shears_outputs = OrderedDict([("shears",1)])
    craft_shears= get_crafting_action("craft-shears", shears_inputs, shears_outputs)

    actions.append(craft_diamond_pickaxe)
    actions.append(craft_shears)

    for block_type in inverse_type_hierarchy["destructible-block"]:
        actions.extend(get_destructible_block_action(block_type, needed_tool = "diamond-pickaxe"))

    sections.extend(actions)
    sections.append(footer)
    domain_s = "\n\n".join(sections)
    print(domain_s)
    return domain_s

def get_crafting_action(name, inputs, outputs, extra_preconditions = tuple()):
    """
    input: Dict[item_type] -> item_count
    output: Dict[item_type] -> item_count
    """
    prefix = f"""(:action {name}
    :parameters ( ?ag - agent )"""
    suffix = "\n)"

    precondition_prefix = "    :precondition ( and\n                      "
    precondition_suffix = "\n                  )"

    preconds = []
    for item_type, item_count in inputs.items():
        preconds.append(f"( > (agent-num-{item_type} ?ag) {item_count} )")

    preconds.extend(extra_preconditions)
    precond_body = "\n                      ".join(preconds)
    precond_s = precondition_prefix + precond_body + precondition_suffix

    effects_prefix = "    :effect (and "
    effects_suffix = ")"
    effects = []
    for item_type, item_count in outputs.items():
        effects.append(f"(increase (agent-num-{item_type} ?ag) {item_count})")
    effects_body = "\n        ".join(effects)
    effects_s = effects_prefix + effects_body + effects_suffix

    return "\n".join([prefix, precond_s, effects_s, suffix])
def make_instance_1(start_with_pick = True, use_bedrock_boundaries = False):
    object_names = OrderedDict()
    object_names["obsidian-block"] = ["obsidian0", "obsidian1"]
    object_names["agent"] = ["steve"]
    object_names["diamond-pickaxe"] = ["old-pointy"]
    object_names["diamond"] = ["dmd0","dmd1","dmd2"]
    object_names["stick"] = ["stick0", "stick1"]

    tgt_obsidian = object_names["obsidian-block"][0]

    header = """(define (problem MINECRAFTCONTRIVED-1)
    (:domain minecraft-contrived)"""

    goal = f"""(:goal (and
            (not (block-present {tgt_obsidian} ))
        )
    )

    """
    x_min, x_max = 0, 2
    y_min, y_max = 0, 2
    z_min, z_max = 0, 2

    # item_counts = OrderedDict([("apple",2),("potato",1)])
    # item_counts = OrderedDict([("apple",1)])
    agent_name = "steve"
    init_conds = []
    init_conds.extend(get_init_location_conds((0,0,0),agent_name))
    inventory_count = OrderedDict()
    for item_type in item_types:
        inventory_count[item_type] = 0
    if start_with_pick:
        inventory_count["diamond-pickaxe"] = 1
    for item_type, item_count in inventory_count.items():
        init_conds.append(f"( = ( agent-num-{item_type} {agent_name} ) {item_count} )")
    # init_conds.append(f"( = ( agent-num-diamond-pickaxe {agent_name} ) 1 )")
    init_conds.extend(get_init_location_conds((0,3,1),tgt_obsidian))
    init_conds.extend(get_init_location_conds((0,3,2),object_names["obsidian-block"][1]))
    for s in object_names["obsidian-block"]:
        init_conds.append(f"( = ( block-hits {s} ) 0 )")
    diamond_pick_name = object_names["diamond-pickaxe"][0]
    init_conds.extend(get_init_location_conds((0,0,0), diamond_pick_name))
    init_conds.append(f"( not ( present {diamond_pick_name} ) )")

    for i, s in enumerate(object_names["stick"]):
        init_conds.extend(get_init_location_conds((1,i,0),s))
        init_conds.append(f"( present {s} )")
    
    for i, s in enumerate(object_names["diamond"]):
        init_conds.extend(get_init_location_conds((2,i,0),s))
        init_conds.append(f"( present {s} )")

    for s in object_names["obsidian-block"]:
        init_conds.append(f"(block-present {s})")


    if use_bedrock_boundaries:
        boundary_positions = get_boundary_positions(x_min, x_max, y_min, y_max, z_min, z_max)
        object_names["bedrock-block"] = [f"bed{i}" for i in range(len(boundary_positions))]
        for i in range(len(boundary_positions)):
            init_conds.extend(get_init_location_conds(boundary_positions[i], object_names["bedrock-block"][i]))

    init_conds = make_init_conds_str(init_conds)
    object_declaration = get_object_declarations(object_names)

    prob_parts = [header, object_declaration, init_conds, goal, ")"]
    prob_s = "\n\n\n".join(prob_parts)

    # bedrock_path_str = "-bedrock" if use_bedrock_boundaries else ""
    # tgt_path = f"examples/minecraft/prob-01{bedrock_path_str}.pddl"
    # print(prob_s)
    # with open(tgt_path, "w") as f:
    #     f.write(prob_s)
    # print(set_objects(item_counts))
    # print(set_initial_conditions(item_counts))
    return prob_s

def make_types_declaration(type_hierarchy):
    inverse_type_hierarchy = invert_dict(type_hierarchy)
    lines = []
    for parent, children in inverse_type_hierarchy.items():
        if parent is None:
            lines.extend(children)
        else:
            l = " ".join(children) + " - " + parent
            lines.append(l)
    types_prefix = "(:types "
    types_suffix = ")"
    types_s = types_prefix + "\n\t" + "\n\t".join(lines) + "\n" + types_suffix
    return types_s
        
if __name__ == "__main__":
    # type_hierarchy = OrderedDict()
    # # locatables have position
    # # items have agent count and present, in addition to location
    # type_hierarchy["locatable"] = None
    # type_hierarchy["agent"] = "locatable"
    # type_hierarchy["item"] = "locatable"
    # item_types = ["apple", "potato", "rabbit", "diamond-axe", "orchid-flower", "daisy-flower"]
    # for i in item_types:
    #     type_hierarchy[i] = "item"
    # print(make_types_declaration(type_hierarchy))
    dom_s = make_domain()
    prob_s = make_instance_1(start_with_pick=True)
    with open("examples/minecraft2/minecraft-contrived2.pddl","w") as f:
        f.write(dom_s)
    with open("examples/minecraft2/prob_obsidian_with_pick.pddl","w") as f:
        f.write(prob_s)

    prob_s = make_instance_1(start_with_pick=False)
    with open("examples/minecraft2/prob_obsidian_without_pick.pddl","w") as f:
        f.write(prob_s)