from dataclasses import dataclass
from typing import Dict, Tuple, List, Set, NewType, Optional, Iterable, TypeVar, Set

import numpy as np
import pandas as pd

alphabet = 'abcdefghijklmnopqrstuvwxyz'

@dataclass(frozen=True, order=True)
class Action:
    name: str
    variables: List[str]
    precondition: List[Tuple[str]]
    effect: List[Tuple[str]]

def build_fact_table(fact_list: List[Tuple[str]], predicate: Tuple[str]) -> pd.DataFrame:
    facts = [fact[1:] for fact in fact_list if fact[0] == predicate]
    assert np.allclose(list(map(len, facts)), len(facts[0]))
    columns = list(alphabet[:len(facts[0])])
    data = pd.DataFrame(facts, columns=columns)
    data.name = predicate
    return data

def initialize_fact_tables(fact_list: List[Tuple[str]]):
    predicate_names = sorted(list(set([fact[0] for fact in fact_list])))
    return {name:build_fact_table(fact_list, name) for name in predicate_names}

def join_preconditions(tables:Dict[str, pd.DataFrame], predicate_list:List[Tuple[str]]) -> pd.DataFrame:
    remapped_tables = []
    for predicate in predicate_list:
        table_name, *params = predicate
        table = tables[table_name]
        column_names = dict(zip(table.columns, params))
        table = table.rename(columns=column_names)
        remapped_tables.append(table)
    result, *rest = remapped_tables
    for table in rest:
        try:
            result = result.merge(table)
        except pd.errors.MergeError:
            result = result.join(table, how='cross')
    return result

def select_effects(groundings_table:pd.DataFrame, predicate_list:Tuple[str]) -> Dict[str, pd.DataFrame]:
    results = {}
    for predicate in predicate_list:
        table_name, *parameters = predicate
        results[table_name] = groundings_table[parameters]
    return results

def extend_fact_tables(tables: Dict[str, pd.DataFrame], updates: Dict[str, pd.DataFrame]) -> bool:
    did_extend = False
    for table_name, new_facts in updates.items():
        table = tables[table_name]
        column_mapping = {new: orig for new, orig in zip(new_facts.columns, table.columns)}
        new_facts = new_facts.rename(columns=column_mapping)
        new_table = pd.concat((table, new_facts)).drop_duplicates()
        if len(new_table) > len(table):
            did_extend = True
        tables[table_name] = new_table
        return did_extend

def generate_next_fact_layer(tables: Dict[str, pd.DataFrame], actions: List[Action]) -> Dict[str, pd.DataFrame]:
    did_extend = False
    for action in actions:
        result = join_preconditions(tables, action.precondition)
        updates = select_effects(result, action.effect)
        did_extend = did_extend or extend_fact_tables(tables, updates)
    return did_extend


def main():
    init_state = [
        ('at', 'obj1', 'l1'),
        ('at', 'obj2', 'l1'),
        ('at', 'obj3', 'l3'),
        ('at', 'obj4', 'l2'),
        ('path', 'l1', 'l2'),
        ('path', 'l1', 'l3'),
        ('path', 'l2', 'l3'),
        ('path', 'l3', 'l4'),
        ('alive', 'steve')
    ]

    a1 = Action(
        name='a1',
        variables = ['x', 'y', 'w', 'z', 'ag'],
        precondition = [
            ('at', 'x', 'y'),
            ('path', 'y', 'w'),
            ('path', 'w', 'z'),
            ('alive', 'steve')
        ],
        effect = [
            ('at', 'x', 'z'),
        ],
    )
    a2 = Action(
        name='a2',
        variables = ['x', 'y', 'w', 'z', 'ag'],
        precondition = [
            ('at', 'x', 'z'),
            ('path', 'y', 'w'),
            ('path', 'w', 'z'),
            ('alive', 'steve')
        ],
        effect = [
            ('at', 'x', 'y'),
        ],
    )
    actions = [a1, a2]
    tables = initialize_fact_tables(init_state)
    while generate_next_fact_layer(tables, actions):
        pass

    tables
