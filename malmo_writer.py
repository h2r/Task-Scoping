from collections import OrderedDict
from itertools import product
import math
import operator as op
from functools import reduce
import copy

type_replacements = {
    "obsidian-block":"obsidian",
    "netherportal":"portal",
    'daisy-flower': 'daisy_flower',
    'diamond-pickaxe': 'diamond_pickaxe',
    'flint-and-steel': 'flint_and_steel',
    'iron-ingot': 'iron_ingot',
    'iron-ore': 'iron_ore',
    'orchid-flower': 'orchid_flower'
}

with open("examples/malmo/block_types.txt", "r") as f:
    valid_block_types = f.read().splitlines()
with open("examples/malmo/item_types.txt", "r") as f:
    valid_item_types = f.read().splitlines()

def pddl2malmo_coords(x,y,z, z_offset = 200):
	# TODO test
	return x, z + z_offset, -y


def draw_item(object_type, x, y, z):
    if object_type not in valid_item_types:
        raise ValueError(f"{object_type} not a valid item type")
    return f'<DrawItem x="{x}" y="{y}" z="{z}" type="{object_type}"/>'
    # return 'x'+index+'="'+x+'" y'+index+'="' +str(y)+'" z'+index+'="'+z+'"'

def draw_block(object_type, x, y, z):
    if object_type not in valid_block_types:
        raise ValueError(f"{object_type} not a valid block type")
    return f'<DrawCuboid x1="{x}" y1="{y}" z1="{z}" x2="{x}" y2="{y}" z2="{z}" type="{object_type}"/>'
    # return 'x'+index+'="'+x+'" y'+index+'="' +str(y)+'" z'+index+'="'+z+'"'

def make_agent_placement(x,y,z):
    x,y,z = float(x), float(y), float(z)
    return f'<Placement x="{x}" y="{y}" z="{z}" pitch="50"/>'

def make_inventory(inventory_counts):
    inventory_lines = []
    slot_id = 0
    for item_type, item_count in inventory_counts.items():
        for _ in range(item_count):
            inventory_lines.append(f'<InventoryItem type="{item_type}" slot="{slot_id}"/>')
            slot_id += 1
    inventory = "\n\t".join(inventory_lines)
    return inventory

def make_arena(x_min, x_max, y_min, y_max, z_min, z_max):
    """
    Returns pair of lines that place bedrock around, and air inside
    """
    bedrock = f'<DrawCuboid x1="{x_min - 1}" y1="{y_min - 1}" z1="{z_min - 1}" x2="{x_max + 1}" y2="{y_max + 1}" z2="{z_max + 1}" type="bedrock"/>'
    air = f'<DrawCuboid x1="{x_min}" y1="{y_min}" z1="{z_min}" x2="{x_max}" y2="{y_max}" z2="{z_max}" type="air"/>'
    return [bedrock, air]

def make_malmo_domain(blocks, items, start_pos, inventory_counts
    , x_min, x_max, y_min, y_max, z_min, z_max
    , summary="Domain for Scoping", convert_coords = True):
    """
    All coordinates are PDDL coordinates. We will convert them to malmo coords.
    blocks: dict[type]-> list of positions. Make sure to only include present blocks
    items: dict[type] -> list of positions. Make sure to only include present items
    inventory: dict[type] -> count in inventory
    start_pos: x,y,z position of agent
    convert_coords: If true, we convert coords to malmo. If false, we assume coords are already in malmo format
    """
    if convert_coords:
        start_pos = pddl2malmo_coords(*start_pos)

        blocks_new = OrderedDict()
        for t, positions in blocks.items():
            blocks[t] = [pddl2malmo_coords(*p) for p in positions]
        blocks = blocks_new
        del blocks_new

        items_new = OrderedDict()
        for t, positions in items.items():
            items[t] = [pddl2malmo_coords(*p) for p in positions]
        items = items_new
        del items_new

        # y is negatized, which swaps max and min
        x_min, y_min, z_min = pddl2malmo_coords(x_min, y_max, z_min)
        x_max, y_max, z_max = pddl2malmo_coords(x_max, y_min, z_max)

    with open("examples/malmo/templates/main_template.xml","r") as f:
        domain = f.read()
    # Used to fill in blanks in template domain
    format_dict = OrderedDict()
    # Set summary
    format_dict["summary"] = summary
    # Set agent start position
    format_dict["placement"] = make_agent_placement(*start_pos)
    # Set agent start inventory
    format_dict["inventory"] = make_inventory(inventory_counts)

    drawing_lines = []
    # Add bedrock and air
    drawing_lines.extend(make_arena(x_min, x_max, y_min, y_max, z_min, z_max))
    # Place blocks in the world
    for t, positions in blocks.items():
        for p in positions:
            drawing_lines.append(draw_block(t,*p))
    # Place items in the world
    for t, positions in items.items():
        for p in positions:
            drawing_lines.append(draw_item(t, *p))
    
    format_dict["drawing_objects"] = "\n".join(drawing_lines)
    
    return domain.format(**format_dict)