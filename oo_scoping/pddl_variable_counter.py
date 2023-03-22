from oo_scoping.PDDLz3 import PDDL_Parser

def pddl_paths_to_state_variable_count(domain: str, problem: str) -> int:
    """Get the count of state variables from domain and problem path"""
    parser = PDDL_Parser()
    parser.parse_domain(domain)
    parser.parse_problem(problem)
    return parser.get_state_variable_count()

if __name__ == "__main__":
    ipc_dir = "oo_scoping/examples/domains/IPC_Domains/CompositeIPC"

    ipc_composite_domain_path = f"{ipc_dir}/ipc_composite.pddl"
    ipc_composite_depot_problem_path = "oo_scoping/examples/domains/IPC_Domains/CompositeIPC/prob-01.pddl"

    ipc_names = {
        "depot": "prob-01",
        "satellite": "prob-02",
        "driverlog": "prob-03",
        "zenotravel": "prob-04"
    }

    for experiment_name, problem_name in ipc_names.items():
        unscoped_problem = f"{ipc_dir}/{problem_name}.pddl"
        scoped_problem = f"{ipc_dir}/{problem_name}_scoped_sans_cl.pddl"
        scoped_domain = f"{ipc_dir}/ipc_composite_scoped_{problem_name}.pddl"
        n_unscoped = pddl_paths_to_state_variable_count(ipc_composite_domain_path, unscoped_problem)
        n_scoped = pddl_paths_to_state_variable_count(scoped_domain, scoped_problem)
        print(f"{experiment_name}: {n_unscoped} -> {n_scoped}")


