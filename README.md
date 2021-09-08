# Task Scoping with VaPAR

## Installation
Make sure to have python 3.7.9 installed (we recommend a virtual or conda environment!). Then, from the root of this repo's directory, run:

```pip install -e .```

## Usage
You will need to run a different command depending on whether your domain and problem PDDL files are propositional or numeric. 

### Propositional Domains
For these domains, we first convert the problem into the SAS+ representation, then run VaPAR to scope the domain and problem.

```python downward_translate/translate_and_scope.py <domain_path> <problem_path> --sas-file <desired_sas_file_name> --scope True```

This will generate 2 files in the current directory: 1 `.sas` file with the name `<desired_sas_file_name>` and 1 with `_scoped` inserted into the name. The latter is the file after VaPAR has been used to scope the original file. Each of these files can then directly be used for planning with Fast Downward or any other planner that uses SAS+ files.

Note: this leverages a PDDL to SAS+ translator taken directly from the [Fast Downward codebase](https://github.com/aibasel/downward).


Example:

```python downward_translate/translate_and_scope.py examples/gripper-painting-domain/domain.pddl examples/gripper-painting-domain/prob04.pddl --sas-file gripper-painting.sas --scope True```

### Numeric Domains
For these domains, we first ground all variables and operators, then run VaPAR on the grounded problem and use this to return "scoped" domain and problem PDDL files.

```python oo_scoping/pddl_scoper.py --domain <path_to_domain_file> --prob <path_to_problem_file>```

Note that this assumes the domain and problem file are within the same directory.

The scoped domain and problem will be placed in the same directories as the input domain and problem. Use the scoped problem that ends with "with_cl". The file that says "sans_cl" may remove some causally-linked objects that, in principle, can be ignored, but maybe unsafe to remove (this discrepancy arises because VaPAR identifies *grounded* state-variables and operators to remove, whereas PDDL files are lifted by default).

Example:

```python oo_scoping/pddl_scoper.py --domain examples/multi_monkeys_playroom/multi_monkeys_playroom.pddl --prob examples/multi_monkeys_playroom/prob01.pddl```

## Running Experiments from paper
Prerequisite: Clone the Fast Downward repository from [here](https://github.com/aibasel/downward). Make sure the `fast-downward.py` file at the root of the repo can run properly - you will need to specify the path to this file to run experiments (explained below).

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