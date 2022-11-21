from oo_scoping.PDDL import PDDL_Parser
import random
import argparse
import tempfile

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


def add_irrel_goals_to_prob_file(domain, problem, **kwargs):
    goal_conds = find_new_irrel_goal_clauses(domain, problem)
    wf = tempfile.NamedTemporaryFile(mode="w+t")
    lines_to_be_written = []
    with open(problem, 'r') as rf:
        lines = rf.readlines()
        in_goal = False
        for line in lines:
            if in_goal:
                for goal_cond in goal_conds:
                    new_goal_cond_str = '\t(' + ' '.join(goal_cond) + ')\n'
                    lines_to_be_written.append(new_goal_cond_str)
                in_goal = False
            if "goal" in line.strip():
                in_goal = True
            lines_to_be_written.append(line)
    wf.writelines(lines_to_be_written)
    wf.seek(0)
    return wf

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--domain",type=str,help="Path location of the PDDL domain file")
    parser.add_argument("--problem",type=str,help="Path location of the PDDL problem file corresponding to the specified domain")
    args = parser.parse_args()
    tmp_file = add_irrel_goals_to_prob_file(args.domain, args.problem, "tmp_prob", **{'verbose': 1})
    print(tmp_file.read())
    tmp_file.close()