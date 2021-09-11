# AWS Readme

These are instructions for running scoping experiments on aws EC2. Note that the results in the paper are from experiments run on a laptop, NOT in EC2. 

## Instance parameters

Type

AMI


## Usage

Copy the scoping_supplement.zip to your ec2 instance with scp:

    scp -i <path2key_file> scoping_supplement.zip ubuntu@<ec2_instance_address>:~/

SSH into the ec2 instance

    ssh -i <path2key_file> ubuntu@<ec2_instance_address>


Unzip the supplement

    unzip scoping_supplement.zip

Mount the planutils docker image

    source scoping_supplement/scoping/ubuntu_scripts/get_enhsp_docker.sh

Change directory to /scoping_supplement

    cd /scoping_supplement

Run config_all.sh to setup conda, fast downward

    source scoping/ubuntu_scripts/config_all.sh

Run ENHSP-2020 experiments using the experiments/enhsp_experiment.py script. The arguments are:

1. Number of runs in this experiment
2. Path to domain file
3. Path to problem file
4. Path to directory the experiment logs will be saved in 

Example command:

    python ./experiments/enhsp_experiment.py 2 examples/multi_monkeys_playroom/multi_monkeys_playroom.pddl examples/multi_monkeys_playroom/prob01.pddl ./experiment_logs/multi_monkeys_playroom_01

**TODO: This crashes because enhsp cannot find the domains. When I run the identical planning command from terminal, it works. I've checked that the working directory is the same from the terminal and from the pythons script.**

Run Fast Downward experiments using the experiments/fd_experiment.py script. The arguments are the same as for the enhsp script.