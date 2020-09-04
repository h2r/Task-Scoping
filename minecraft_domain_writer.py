from collections import OrderedDict
from itertools import product

item_types = ["wool","diamond", "stick", "diamond-pickaxe", "apple", "potato"
    , "rabbit", "orchid-flower", "daisy-flower", "flint", "coal", "iron-ore", "iron-ingot", "netherportal",
    "flint-and-steel"]


# type2name = {
#     "apple":"ap",
#     "potato":"tot",
#     "rabbit":"rab",
#     "diamond-axe":"ax",
#     "orchid-flower":"orc",
#     "daisy-flower":"daisy",
#     "bedrock":"bed"
# }

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
        if t != "netherportal":
            inventory_count_vars.append(f"(agent-num-{t} ?ag - agent)")
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
        if(t != "netherportal"):
            actions.append(action_template.format(t=t))
    return actions

def make_drop_actions(item_types, item_or_block=True):
    if(item_or_block):
        action_template = """(:action drop-{t}
 :parameters (?ag - agent ?i - {t})
 :precondition (and (>= (agent-num-{t} ?ag) 1)
                    (not (present ?i)))
 :effect (and (present ?i)
              (assign (x ?i) (x ?ag))
              (assign (y ?i) (+ (y ?ag) 1))
              (assign (z ?i) (z ?ag))
              (decrease (agent-num-{t} ?ag) 1)
         )
)
"""
    else:
        action_template = """(:action drop-{t}
 :parameters (?ag - agent ?b - {t})
 :precondition (and (>= (agent-num-{t} ?ag) 1)
                    (not (block-present ?b)))
 :effect (and (block-present ?b)
              (assign (x ?b) (x ?ag))
              (assign (y ?b) (+ (y ?ag) 1))
              (assign (z ?b) (z ?ag))
              (decrease (agent-num-{t} ?ag) 1)
         )
)
"""

    actions = []
    for t in item_types:
        if(t != "netherportal" and t != "diamond-pickaxe"):
            actions.append(action_template.format(t=t))
    return actions

def make_netherportal_action():
    action = """(:action open-netherportal
 :parameters (?ag - agent ?ob - obsidian-block ?np - netherportal)
 :precondition (and (>= (agent-num-flint-and-steel ?ag) 1)
                    (= (y ?ob) (+ (y ?ag) 1))
                    (= (z ?ob) (z ?ag))
                    (= (x ?ob) (x ?ag))
                    (block-present ?ob)
                    (not (present ?np))
                )
 :effect (and (present ?np)
              (assign (x ?np) (x ?ob))
              (assign (y ?np) (y ?ob))
              (assign (z ?np) (z ?ob))
         )
)
"""
    return action

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
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (< (block-hits ?b) 4){tool_precond})
    :effect (and (increase (block-hits ?b) 1))
    )"""
    destroy_s = f"""(:action destroy-{block_type}
    :parameters (?ag - agent ?b - {block_type})
    :precondition (and (= (x ?b) (x ?ag))
                        (= (y ?b) (+ (y ?ag) 1))
                        (= (z ?b) (+ (z ?ag) 1))
                        (block-present ?b)
                        (= (block-hits ?b) 3){tool_precond})
    :effect (and (not (block-present ?b))
                 (increase (agent-num-{block_type} ?ag) 1)
            )
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
    type_hierarchy["object"] = None
    type_hierarchy["locatable"] = "object"
    # type_hierarchy["item"] = "object"
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
    predicates.append("(present ?i - item)")  
    predicates.append("(block-present ?b - block)")
    predicates.append("(agent-alive ?ag - agent)")
    functions = []
    functions.append("(block-hits ?b - destructible-block)")
    functions.extend(get_inventory_funcs(inverse_type_hierarchy["item"]))
    functions.extend(get_inventory_funcs(["obsidian-block"]))
    for d in ["x","y","z"]:
        functions.append(f"({d} ?l - locatable)")

    predicates_s = get_predicates_str(predicates)
    sections.append(predicates_s)
    functions_s = get_functions_str(functions)
    sections.append(functions_s)

    actions = []
    actions.append(get_move_actions())
    actions.extend(make_pickup_actions(inverse_type_hierarchy["item"]))
    actions.extend(make_drop_actions(inverse_type_hierarchy["item"]))
    actions.extend(make_drop_actions(inverse_type_hierarchy["destructible-block"], False))

    diamond_pick_inputs = OrderedDict([("stick",2),("diamond",3)])
    diamond_pick_outputs = OrderedDict([("diamond-pickaxe",1)])
    craft_diamond_pickaxe = get_crafting_action("craft-diamond-pickaxe", diamond_pick_inputs, diamond_pick_outputs)
    actions.append(craft_diamond_pickaxe)

    iron_ingot_inputs = OrderedDict([("iron-ore",1),("coal",1)])
    iron_ingot_outputs = OrderedDict([("iron-ingot",1)])
    craft_iron_ingot = get_crafting_action("craft-iron-ingot", iron_ingot_inputs, iron_ingot_outputs)
    actions.append(craft_iron_ingot)

    flint_and_steel_inputs = OrderedDict([("iron-ingot",1),("flint",1)])
    flint_and_steel_outputs = OrderedDict([("flint-and-steel",1)])
    craft_flint_and_steel = get_crafting_action("craft-flint-and-steel", flint_and_steel_inputs, flint_and_steel_outputs)
    actions.append(craft_flint_and_steel)

    for block_type in inverse_type_hierarchy["destructible-block"]:
        actions.extend(get_destructible_block_action(block_type, needed_tool = "diamond-pickaxe"))

    actions.append(make_netherportal_action())

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
        preconds.append(f"( >= (agent-num-{item_type} ?ag) {item_count} )")

    preconds.extend(extra_preconditions)
    precond_body = "\n                      ".join(preconds)
    precond_s = precondition_prefix + precond_body + precondition_suffix

    effects_prefix = "    :effect (and "
    effects_suffix = ")"
    effects = []
    for item_type, item_count in outputs.items():
        effects.append(f"(increase (agent-num-{item_type} ?ag) {item_count})")
    for item_type, item_count in inputs.items():
        effects.append(f"(decrease (agent-num-{item_type} ?ag) {item_count})")
    effects_body = "\n        ".join(effects)
    effects_s = effects_prefix + effects_body + effects_suffix

    return "\n".join([prefix, precond_s, effects_s, suffix])

def make_instance_1(start_with_pick = True, use_bedrock_boundaries = False, add_irrel_items = False, goal_var = ""):
    object_names = OrderedDict()
    # object_names["obsidian-block"] = ["obsidian0", "obsidian1", "obsidian2", "obsidian3", "obsidian4", "obsidian5", "obsidian6", "obsidian7", "obsidian8", "obsidian9"]
    object_names["obsidian-block"] = ["obsidian0", "obsidian1"]
    object_names["agent"] = ["steve"]
    object_names["diamond-pickaxe"] = ["old-pointy"]
    object_names["diamond"] = ["dmd0","dmd1","dmd2"]
    object_names["stick"] = ["stick0", "stick1"]
    object_names["flint"] = ["flint0", "flint1", "flint2"]
    object_names["iron-ore"] = ["iron-ore0"]
    object_names["coal"] = ["coal0"]
    object_names["iron-ingot"] = ["iron-ingot0"]
    object_names["netherportal"] = ["netherportal0"]
    object_names["flint-and-steel"] = ["flint-and-steel0"]

    if(add_irrel_items):
        object_names["apple"] = ["apple1", "apple2", "apple3"]
        object_names["potato"] = ["potato1", "potato2", "potato3", "potato4", "potato5"]
        object_names["orchid-flower"] = ["orchid-flower1", "orchid-flower2", "orchid-flower3", "orchid-flower4", "orchid-flower5"]
        object_names["daisy-flower"] = ["daisy-flower1", "daisy-flower2", "daisy-flower3", "daisy-flower4", "daisy-flower5"]
        object_names["rabbit"] = ["rabbit1", "rabbit2", "rabbit3", "rabbit4", "rabbit5"]

    tgt_obsidian = object_names["obsidian-block"][0]
    tgt_netherpotal = object_names["netherportal"][0]
    agent_name = "steve"

    header = """(define (problem MINECRAFTCONTRIVED-1)
    (:domain minecraft-contrived)"""

    if (goal_var == "break_obsidian"):
        goal = f"""(:goal (and
                (not (block-present {tgt_obsidian} ))
                (= (x {agent_name}) 3)
                (= (y {agent_name}) 4)
                (= (z {agent_name}) 0)
            )
        )
        """
    elif (goal_var == "make_netherportal"):
        goal = f"""(:goal (and 
                            (present {tgt_netherpotal})
                            (= (x {tgt_netherpotal}) 11)
                            (= (y {tgt_netherpotal}) 7)
                            (= (z {tgt_netherpotal}) 0)
                          )
        )
        """
    elif(goal_var == "make_flint_and_steel"):
        goal = f"""(:goal (and
                ( = ( agent-num-flint-and-steel {agent_name} ) 1 )
                (= (x {agent_name}) 11)
                (= (y {agent_name}) 2)
                (= (z {agent_name}) 0)
                )
            )"""

    x_min, x_max = 0, 2
    y_min, y_max = 0, 2
    z_min, z_max = 0, 2

    # item_counts = OrderedDict([("apple",2),("potato",1)])
    # item_counts = OrderedDict([("apple",1)])
    
    init_conds = [f"(agent-alive {agent_name})"]
    init_conds.extend(get_init_location_conds((0,0,0),agent_name))
    inventory_count = OrderedDict()
    for item_type in item_types:
        inventory_count[item_type] = 0
    if start_with_pick:
        inventory_count["diamond-pickaxe"] = 1
    for item_type, item_count in inventory_count.items():
        if item_type != "netherportal":
            init_conds.append(f"( = ( agent-num-{item_type} {agent_name} ) {item_count} )")
    # init_conds.append(f"( = ( agent-num-diamond-pickaxe {agent_name} ) 1 )")
    init_conds.extend(get_init_location_conds((11,7,1),tgt_obsidian))
    init_conds.extend(get_init_location_conds((10,7,0),object_names["obsidian-block"][1]))
    # init_conds.extend(get_init_location_conds((12,7,0),object_names["obsidian-block"][2]))
    # init_conds.extend(get_init_location_conds((10,7,1),object_names["obsidian-block"][3]))
    # init_conds.extend(get_init_location_conds((12,7,1),object_names["obsidian-block"][4]))
    # init_conds.extend(get_init_location_conds((10,7,2),object_names["obsidian-block"][5]))
    # init_conds.extend(get_init_location_conds((12,7,2),object_names["obsidian-block"][6]))
    # init_conds.extend(get_init_location_conds((10,7,3),object_names["obsidian-block"][7]))
    # init_conds.extend(get_init_location_conds((12,7,3),object_names["obsidian-block"][8]))
    # init_conds.extend(get_init_location_conds((11,7,3),object_names["obsidian-block"][9]))

    for s in object_names["obsidian-block"]:
        init_conds.append(f"( = ( block-hits {s} ) 0 )")
    init_conds.append("(= (agent-num-obsidian-block steve) 0)")
    diamond_pick_name = object_names["diamond-pickaxe"][0]
    init_conds.extend(get_init_location_conds((0,0,0), diamond_pick_name))
    init_conds.append(f"( not ( present {diamond_pick_name} ) )")

    for i, s in enumerate(object_names["stick"]):
        init_conds.extend(get_init_location_conds((1,i,0),s))
        init_conds.append(f"( present {s} )")

    for i, s in enumerate(object_names["flint"]):
        init_conds.extend(get_init_location_conds((8,i,0),s))
        init_conds.append(f"( present {s} )")

    for i, s in enumerate(object_names["iron-ore"]):
        init_conds.extend(get_init_location_conds((10,i,0),s))
        init_conds.append(f"( present {s} )")
    
    for i, s in enumerate(object_names["coal"]):
        init_conds.extend(get_init_location_conds((9,i,0),s))
        init_conds.append(f"( present {s} )")
    
    for i, s in enumerate(object_names["diamond"]):
        init_conds.extend(get_init_location_conds((2,i,0),s))
        init_conds.append(f"(present {s})")

    for i, s in enumerate(object_names["iron-ingot"]):
        init_conds.extend(get_init_location_conds((0,i,0),s))
        init_conds.append(f"(not ( present {s} ))")

    for i, s in enumerate(object_names["flint-and-steel"]):
        init_conds.extend(get_init_location_conds((0,i,0),s))
        init_conds.append(f"(not ( present {s} ))")

    for i, s in enumerate(object_names["netherportal"]):
        init_conds.extend(get_init_location_conds((0,i,0),s))
        init_conds.append(f"(not ( present {s} ))")

    if(add_irrel_items):
        for i, s in enumerate(object_names["apple"]):
            init_conds.extend(get_init_location_conds((3,i,0),s))
            init_conds.append(f"( present {s} )")

        for i, s in enumerate(object_names["potato"]):
            init_conds.extend(get_init_location_conds((4,i,0),s))
            init_conds.append(f"( present {s} )")

        for i, s in enumerate(object_names["daisy-flower"]):
            init_conds.extend(get_init_location_conds((5,i,0),s))
            init_conds.append(f"( present {s} )")

        for i, s in enumerate(object_names["orchid-flower"]):
            init_conds.extend(get_init_location_conds((6,i,0),s))
            init_conds.append(f"( present {s} )")

        for i, s in enumerate(object_names["rabbit"]):
            init_conds.extend(get_init_location_conds((7,i,0),s))
            init_conds.append(f"( present {s} )")

    for s in object_names["obsidian-block"]:
        init_conds.append(f"(block-present {s})")


    if use_bedrock_boundaries:
        boundary_positions = get_boundary_positions(x_min, x_max, y_min, y_max, z_min, z_max)
        object_names["bedrock"] = [f"bed{i}" for i in range(len(boundary_positions))]
        for i in range(len(boundary_positions)):
            s = object_names["bedrock"][i]
            init_conds.extend(get_init_location_conds(boundary_positions[i], s))
            init_conds.append(f"(block-present {s})")
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
            pass
            # from IPython import embed; embed()
            # lines.extend(children)
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
    with open("examples/minecraft2/minecraft-contrived2.pddl","w") as f:
        f.write(dom_s)
    prob_s = make_instance_1(start_with_pick=True, add_irrel_items=False, goal_var="make_netherportal")
    with open("examples/minecraft2/prob_nether_with_pick.pddl","w") as f:
        f.write(prob_s)
    prob_ir = make_instance_1(start_with_pick=True, add_irrel_items=True, goal_var="make_netherportal")
    with open("examples/minecraft2/prob_irrel_nether_with_pick.pddl","w") as f:
        f.write(prob_ir)
    
    prob_s = make_instance_1(start_with_pick=True, add_irrel_items=False, goal_var="break_obsidian")
    with open("examples/minecraft2/prob_obsidian_with_pick.pddl","w") as f:
        f.write(prob_s)
    prob_ir = make_instance_1(start_with_pick=True, add_irrel_items=True, goal_var="break_obsidian")
    with open("examples/minecraft2/prob_irrel_obsidian_with_pick.pddl","w") as f:
        f.write(prob_ir)
    
    prob_s = make_instance_1(start_with_pick=True, add_irrel_items=False, goal_var="make_flint_and_steel")
    with open("examples/minecraft2/prob_flint_with_pick.pddl","w") as f:
        f.write(prob_s)
    prob_ir = make_instance_1(start_with_pick=True, add_irrel_items=True, goal_var="make_flint_and_steel")
    with open("examples/minecraft2/prob_irrel_flint_with_pick.pddl","w") as f:
        f.write(prob_ir)