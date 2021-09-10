#!/bin/bash
# This wget works when run directly in terminal, but not when run as part of this script. I don't know why. 
# Maybe carriage returns are causing issues?
wget https://repo.anaconda.com/miniconda/Miniconda3-py39_4.10.3-Linux-x86_64.sh
bash Miniconda3-py39_4.10.3-Linux-x86_64.sh -b -p ~/miniconda
chown 1000:1000 /home/ubuntu/.conda
eval "$(~/miniconda/bin/conda shell.bash hook)"
conda create -n scoping python=3.7.9 -y
conda activate scoping
pip install pandas