# Experiments on AWS Plan

We plan to re-run our experiments on AWS to

1. Improve reproducibility
2. Gather effective state space metrics (states visited/expanded/etc)
3. Reduce timing variance by
   1. Using more experiments
   2. Using more consistent computing environment - an ec2 instance will not be distracted with other tasks



## Deployment Plan - Overview

Create docker image that is able to run our experiment scripts with no further modifications to the environment. The image will be (roughly) equivalent to the planutils image after installing fast downward and setting up the scoping conda environment. 

Create a job-template that takes the following parameters:

1. Experiment Name (eg. Monkeys1)
2. Domain path
3. Problem path
4. Trial number
5. Planner

We will run a job for each experiment, for each trial number, and upload the logs to the s3 location f"s3://scoping/experiment_logs/{experiment_name}/{trial_number}"

Afterwards, compile the results into csvs. From the csvs generate plots and tables for Latex.


## Deployment Framework Candidates

### Python Script using Boto3

Just write a python script that spins up the instances and tells them to run a command (or 2) using boto3, wait until the commands are done, then compile results.

**Pro:** Simple
**Con:** Michael doesn't know whether this is in fact simple to do with boto3. It seems like it obviously should be, but sometimes things are weirdly complicated.

### Ansible

**Pro:** Michael has used Ansible before

**Con:** Ansible may not support DAGs. If not, we will have to run the compilation job manually. Not a big issue, but if we're going to get into some tool, I'd like it to be a tool that will generalize well.

### Airflow

**Pro:**

1. Supports DAGs
2. Michael hears it is nice
3. Michael may use it for work in the future and would be interested in learning it now