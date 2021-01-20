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
python downward_translate/translate.py /home/<redacted>/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/domain.pddl /home/<redacted>/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/prob-01.pddl --sas-file output.sas
```
## Common problems / bugs
1. Task Scoping commented out everything in my problem and domain files!!!
    1. Check if your goal is already solved in the initial state
    1. If not, there is likely some kind of contradiction in your initial state definition in your problem file. A contradiction causes our algorithm to think that the goal is already satisfied in the initial state by the [Principle of Explosion](https://en.wikipedia.org/wiki/Principle_of_explosion). These contradictions might be very subtle and are most often just re-declarations of the value of a variable (e.g. saying (= (agent-x steve) 4) on one line and (= (agent-x steve) 3) on another line in your problem file)