item_types = ["apple", "potato", "rabbit", "diamond-axe", "orchid-flower", "daisy-flower"]
inventory_types = ["apples", "potatoes", "orchids", "daisies", "raw-rabbits", "cooked-rabbits"]
n_apples = 1
n_agents = 1
apples = [f"apple{i}" for i in range(n_apples)]
agents = ["steve"]

def set_initial_conditions(agents, apples):
    init_s_prefix = "(:init"
    init_s_suffix = ")"
    init_conds = []
    for i, a in enumerate(agents):
        init_conds.append(f"(= (agent-x {a}) {i})")
        init_conds.append(f"(= (agent-y {a}) 0)")
        init_conds.append(f"(= (agent-z {a}) 0)")
        init_conds.append(f"( agent-has-pickaxe {a} )")
        for item_type in inventory_types:
            init_conds.append(f"(= (agent-num-{item_type} {a}) 0)")

    for i, a in enumerate(apples):
        init_conds.append(f"(= (apple-x {a}) {i})")
        init_conds.append(f"(= (apple-y {a}) 1)")
        init_conds.append(f"(= (apple-z {a}) 0)")
        init_conds.append(f"( apple-present {a} )")
    init_s = init_s_prefix + "\n\t" + "\n\t".join(init_conds) + "\n" + init_s_suffix
    return init_s

print(set_initial_conditions(agents, apples))