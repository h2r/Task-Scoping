#!/bin/bash
# Install fast downwards
# Can I skip this part?
git clone https://github.com/aibasel/downward.git
# Change owner to user
sudo chown -R ubuntu downward/
cd downward
./build.py
