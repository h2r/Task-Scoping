from dataclasses import dataclass
from typing import Dict, Tuple, List, Set, NewType, Optional, Iterable, TypeVar, Set

import numpy as np
import pandas as pd

alphabet = 'abcdefghijklmnopqrstuvwxyz'

init_state = [
    ('at', 'obj1', 'l1'),
    ('at', 'obj2', 'l1'),
    ('at', 'obj3', 'l3'),
    ('at', 'obj4', 'l2'),
    ('path', 'l1', 'l2'),
    ('path', 'l1', 'l3'),
    ('path', 'l2', 'l3'),
    ('path', 'l3', 'l4'),
    ('alive', 'agent')
]

@dataclass(frozen=True, order=True)
class Action:
    name: str
    variables: List[str]
    precondition: List[Tuple[str]]
    effect: List[Tuple[str]]

a1 = Action(
    name='a1',
    variables = ['x', 'y', 'w', 'agent'],
    precondition = [
        ('at', 'x', 'y'),
        ('path', 'y', 'w'),
        ('path', 'w', 'z'),
        # ('alive', 'agent')
    ],
    effect = [
        ('at', 'x', 'z'),
    ],
)

def get_facts(fact_list, predicate):
    facts = [fact[1:] for fact in fact_list if fact[0] == predicate]
    assert np.allclose(list(map(len, facts)), len(facts[0]))
    return facts

facts = get_facts(init_state, 'at')

def build_fact_table(fact_list, predicate):
    facts = get_facts(fact_list, predicate)
    columns = list(alphabet[:len(facts[0])])
    data = pd.DataFrame(facts, columns=columns)
    data.name = predicate
    return data

tables = [build_fact_table(init_state, name) for name in ['at', 'path', 'alive']]

def merge(tables:List[pd.DataFrame], predicate_list:List[Tuple[str]]):
    remapped_tables = []
    tables_dict = {table.name: table for table in tables}
    for predicate in predicate_list:
        table_name, *params = predicate
        table = tables_dict[table_name]
        column_names = dict(zip(table.columns, params))
        table = table.rename(columns=column_names)
        remapped_tables.append(table)

    result = None
    for table in remapped_tables:
        if result is None:
            result = table
        else:
            result = result.merge(table)

    return result

result = merge(tables, a1.precondition)
