#!/bin/bash
declare -a arr=("do_apt_get.sh" "config_aws.sh" "config_git.sh" "config_conda.sh" "install_fast_downward.sh")
# Save the working directory. We will come back here after sourcing each script
cd /mnt/scoping
cwd=$(pwd)

for i in "${arr[@]}"
do
   echo "$i"
   source ubuntu_scripts/"$i"
   cd $cwd
done