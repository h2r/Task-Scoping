# Task Scoping

## Usage
Use python 3.7.9 (other versions may work)

    pip install -r requirements.txt
    python scoping_cli.py <domain_path> <problem_path>

Example:

    python pddl_scoper.py "domains/multi_monkeys_playroom copy/multi_monkeys_playroom.pddl" "domains/multi_monkeys_playroom copy/prob-02.pddl"

The scoped domain and problem will be placed in the same directories as the input domain and problem. Use the scoped problem that ends with "with_cl". The file that says "sans_cl" may remove some causally-linked objects that, in principle, can be ignored, but due to limitations of PDDL we cannot always remove them safely.

### Scoping SAS+
Note: PDDL to SAS+ translator copied directly from the Fast Downward Planner codebase. All 

Example command for monkeys domain:
```
python3 downward_translate/translate.py /home/nishanth/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/domain.pddl /home/nishanth/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/prob-01.pddl --sas-file output.sas
```
