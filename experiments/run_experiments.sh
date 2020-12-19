#!/bin/bash

COUNTER=10
until [ $COUNTER -lt 1 ]; do
    echo RUN_NUMBER $COUNTER
    ./time_planner.sh
    ./time_scoper_and_planner.sh
    let COUNTER-=1
done