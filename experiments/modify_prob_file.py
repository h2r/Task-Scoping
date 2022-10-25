from oo_scoping.PDDL import PDDL_Parser
import random
import argparse

def find_new_irrel_goal_clauses(domain, problem, **kwargs):
    """
    :param domain: Path of domain file
    :param problem: Path of problem file
    """
    parser = PDDL_Parser()
    parser.parse_domain(domain)
    parser.parse_problem(problem)

    # First, find the predicates that appear in the goal.
    goal_pred_names = set()
    for g_clause in parser.positive_goals + parser.negative_goals:
        goal_pred_names.add(g_clause[0])

    # Next, find all initial conditions that use these predicates.
    init_conds_with_goal_pred = []
    for init_clause in parser.state:
        if init_clause[0] in goal_pred_names:
            init_conds_with_goal_pred.append(init_clause)

    # Finally, find the initial conditions that are not already
    # goal atoms.
    conditional_irrel_candidates = []
    for init_clause in init_conds_with_goal_pred:
        if init_clause not in parser.positive_goals + parser.negative_goals:
            conditional_irrel_candidates.append(init_clause)

    # Randomly generate some number of conditionally-irrelevant clauses
    # to add to the goal.
    num_irrel_to_add = random.choice(range(1, len(conditional_irrel_candidates)))
    goal_conds_to_add = random.sample(conditional_irrel_candidates, num_irrel_to_add)

    return goal_conds_to_add

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--domain",type=str,help="Path location of the PDDL domain file")
    parser.add_argument("--problem",type=str,help="Path location of the PDDL problem file corresponding to the specified domain")
    args = parser.parse_args()
    find_new_irrel_goal_clauses(args.domain, args.problem, **{'verbose': 1})