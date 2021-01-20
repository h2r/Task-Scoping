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
python downward_translate/translate.py /home/<user>/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/domain.pddl /home/<user>/Documents/planutils_stuff/OO-Scoping-IPC/oo_scoping/examples/domains/multi_monkeys_playroom_strips/prob-01.pddl --sas-file output.sas
```

## Running Experiments
1. There is a sub-folder under the `experiments/` folder for every domain that we evaluated task scoping on for our paper
1. Within each of these sub-folders, there is a bash script that contains the name of the problem file it runs experiments on.
    1. For the IPC domains (`driverlog-domain`,`logistics-domain`,`gripper-domain`,`satellite-domain`,`zenotravel-domain`), each bash script takes exactly 2 arguments:
        1. The number of trials you wish to run (for our paper, we use 5)
        1. The location of the `fast-downward.py` file that comes with an installation of [The Fast Downward Planning System Repository](http://www.fast-downward.org/ObtainingAndRunningFastDownward)
    - The script will run the experiment and print out times, along with their labels, to your terminal after completion
    - For example, to run 5 experiment trials on logistics domain prob 15, simply call:
        ```
        ./experiments/logistics-domain/run_logistics15_experiments.sh 5 /home/<user>/Documents/downward/fast-downward.py
        ```
    
    1. For the Numeric PDDL 2.1 domains (`monkeys-playroom-numeric-domain` and `minecraft-domain`), you will require the ENHSP-2020 planner, which you can obtain by installing and launching [planutils](https://pypi.org/project/planutils/) and then running the command: `enhsp-2020` and answering `y` to the prompt to install this planner. To get any results for planning times, you must execute a bash script from within an environment where the `enhsp-2020` command is recognized and works correctly (so if you use planutils, you can execute these bash scripts from within the activated Singularity container!). Each of the bash scripts within these folders will have bash scripts that take the following arguments
        1. The number of trials you wish to run (for our paper, we use 5)
        1. `scope_true`: an optional argument. Include this to task scoping before planning
    - The script will run the experiment and print out times, along with their labels, to your terminal after completion
    - For example, if you want to run experiments on the plank-making task from the Minecraft domain for 5 trials with task scoping as a preprocessing step, run:
        ```
        ./experiments/minecraft-domain/run_minecraftPlankMaking_experiments.sh 5 scope_true
        ```
    - And if you'd like to run the same task for the same number of trials without scoping, run:
        ```
        ./experiments/minecraft-domain/run_minecraftPlankMaking_experiments.sh 5
        ```

## Common problems / bugs
1. Task Scoping commented out everything in my problem and domain files!!!
    1. Check if your goal is already solved in the initial state
    1. If not, there is likely some kind of contradiction in your initial state definition in your problem file. A contradiction causes our algorithm to think that the goal is already satisfied in the initial state by the [Principle of Explosion](https://en.wikipedia.org/wiki/Principle_of_explosion). These contradictions might be very subtle and are most often just re-declarations of the value of a variable (e.g. saying (= (agent-x steve) 4) on one line and (= (agent-x steve) 3) on another line in your problem file)