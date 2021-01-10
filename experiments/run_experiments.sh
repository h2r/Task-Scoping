#!/bin/bash

COUNTER=1
until [ $COUNTER -lt 1 ]; do
    echo RUN_NUMBER $COUNTER
    python ./downward_translate/translate_and_scope.py examples/IPC_domains_propositional/logistics00/domain.pddl examples/IPC_domains_propositional/logistics00/prob15.pddl --sas-file logistics15.sas
    let COUNTER-=1
done