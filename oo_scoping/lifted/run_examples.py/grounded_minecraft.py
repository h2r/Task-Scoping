from oo_scoping.lifted.enumerated_operators_like_og_scoping import EnumeratedPDDLTask

from oo_scoping.examples.paths import Minecraft3Paths

if __name__ == "__main__":
    task = EnumeratedPDDLTask.from_domain_and_problem_files(Minecraft3Paths.domain, Minecraft3Paths.planks_irrel)
    # relevant_operators = task.scope()
    # for o in relevant_operators.operators_grounded:
    #     print("~~~~~~~~~")
    #     print(o)

    rel_vars = task.scope()
    for p in rel_vars.pvar_names:
        print(p)
