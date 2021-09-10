#!/bin/bash
docker pull aiplanning/planutils
docker run --privileged -v /etc/localtime:/etc/localtime -v /home/ubuntu/ubuntu_scripts/mnt_wrap:/mnt/ -it aiplanning/planutils bash
echo "loaded planutils container"