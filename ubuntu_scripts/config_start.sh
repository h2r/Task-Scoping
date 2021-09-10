#!/bin/bash
echo Gettin
declare -a arr=("do_apt_get.sh" "config_aws.sh" "config_git.sh" "config_conda.sh" "instal_fast_downward.sh" "get_enhsp_docker.sh")
# config_conda.sh doens't work. wget fails, chmod fails, conda adding conda to shell fails, conda create fails, conda activate fails

for i in "${arr[@]}"
do
   echo "$i"
   source "$i"
done