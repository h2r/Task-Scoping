import re, os, argparse


def get_plan_metrics(plan_path):
    patterns = {
        "length": "Plan length: (\d+) step\(s\)",
        "cost": "Plan cost: (\d+)",
        "states_expanded": "Expanded (\d+) state\(s\).",
        "states_reopened": "Reopened (\d+) state\(s\).",
        "states_evaluated": "Evaluated (\d+) state\(s\).",
        "states_generated": "Generated (\d+) state\(s\).",
        "states_expanded_until_last_jump":"Expanded until last jump: (\d+) state\(s\)."
    }

    with open(plan_path, "r") as f:
        s_plan = f.read()
    plan_metrics = {}
    for k, pat in patterns.items():
        a = re.search(pat, s_plan)
        if a is None:
            raise ValueError(f"Could not find metric {k} in plan log")
        plan_metrics[k] = a.group(1)
    return plan_metrics

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("plan_path", type=str)
    args = parser.parse_args()

    # plan_path = "experiment_logs/logistics15/0/plan_scoped/stdout.txt"
    plan_path = args.plan_path
    plan_metrics = get_plan_metrics(plan_path)
    print(plan_metrics)