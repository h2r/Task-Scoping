import argparse
import sys


def parse_args():
    argparser = argparse.ArgumentParser()
    # Made these two args optional so that we can run translate_and_scope.main_from_other_script()
    argparser.add_argument(
        "domain", help="path to domain pddl file", nargs="?", default=None
    )
    argparser.add_argument(
        "task", help="path to task pddl file", nargs="?", default=None
    )
    argparser.add_argument(
        "--relaxed",
        dest="generate_relaxed_task",
        action="store_true",
        help="output relaxed task (no delete effects)",
    )
    argparser.add_argument(
        "--full-encoding",
        dest="use_partial_encoding",
        action="store_false",
        help="By default we represent facts that occur in multiple "
        "mutex groups only in one variable. Using this parameter adds "
        "these facts to multiple variables. This can make the meaning "
        "of the variables clearer, but increases the number of facts.",
    )
    argparser.add_argument(
        "--invariant-generation-max-candidates",
        default=100000,
        type=int,
        help="max number of candidates for invariant generation "
        "(default: %(default)d). Set to 0 to disable invariant "
        "generation and obtain only binary variables. The limit is "
        "needed for grounded input files that would otherwise produce "
        "too many candidates.",
    )
    argparser.add_argument(
        "--sas-file",
        default="output.sas",
        help="path to the SAS output file (default: %(default)s)",
    )
    argparser.add_argument(
        "--sas-file-correct",
        default=None,
        help="path to the correctly scoped SAS output file. When not None, we check that our output matches this correct output. (default: %(default)s)",
    )
    argparser.add_argument(
        "--scope",
        default=False,
        help="Whether or not to run scoping (default: %(default)s)",
    )
    argparser.add_argument(
        "--invariant-generation-max-time",
        default=300,
        type=int,
        help="max time for invariant generation (default: %(default)ds)",
    )
    argparser.add_argument(
        "--add-implied-preconditions",
        action="store_true",
        help="infer additional preconditions. This setting can cause a "
        "severe performance penalty due to weaker relevance analysis "
        "(see issue7).",
    )
    argparser.add_argument(
        "--keep-unreachable-facts",
        dest="filter_unreachable_facts",
        action="store_false",
        help="keep facts that can't be reached from the initial state",
    )
    argparser.add_argument(
        "--skip-variable-reordering",
        dest="reorder_variables",
        action="store_false",
        help="do not reorder variables based on the causal graph. Do not use "
        "this option with the causal graph heuristic!",
    )
    argparser.add_argument(
        "--keep-unimportant-variables",
        dest="filter_unimportant_vars",
        action="store_false",
        help="keep variables that do not influence the goal in the causal graph",
    )
    argparser.add_argument(
        "--dump-task",
        action="store_true",
        help="dump human-readable SAS+ representation of the task",
    )
    argparser.add_argument(
        "--write-erfs",
        default=False,
        help="Whether or not to save file listing effectively relevant fluents (default: %(default)s)",
    )
    return argparser.parse_args()


def copy_args_to_module(args):
    module_dict = sys.modules[__name__].__dict__
    for key, value in vars(args).items():
        module_dict[key] = value


def setup():
    args = parse_args()
    copy_args_to_module(args)


setup()
