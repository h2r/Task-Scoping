import os, enum
from subprocess import CompletedProcess
from oo_scoping.fd_helpers import plan

def print_completed_process(r: CompletedProcess[bytes]) -> None:
    print(f"Return code: {r.returncode}")
    print(f"stderr:\n{r.stderr}")
    print(f"stdout:\n{r.stdout}")

class FDSearchConfigs(enum.Enum):
    # From https://www.fast-downward.org/Doc/Evaluator?highlight=%28dfp%29
    SCC_DFP = ("--evaluator", "merge_and_shrink(shrink_strategy=shrink_bisimulation(greedy=false),merge_strategy=merge_sccs(order_of_sccs=topological,merge_selector=score_based_filtering(scoring_functions=[goal_relevance,dfp,total_order])),label_reduction=exact(before_shrinking=true,before_merging=false),max_states=50k,threshold_before_merge=1)")

if __name__ == "__main__":

    this_dir = os.path.dirname(__file__)
    repo_root = os.path.dirname(os.path.dirname(this_dir))
    example_sas_pth = os.path.join(repo_root, "examples/sas_generated/gripper04.sas")

    r = plan(example_sas_pth, config_args=FDSearchConfigs.SCC_DFP.value)
    print_completed_process(r)