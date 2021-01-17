import os
from oo_scoping.paths import repo_dir
from translate_and_scope import main_from_other_script

# domains_list_path = f"{repo_dir}/misc/scope_cmds.txt"
# with open(domains_list_path, "r") as f:
#     cmd_list = f.read().splitlines()

# for cmd in cmd_list[:1]:
#     print(cmd)
#     os.system(cmd)

tas_kwargs = {
    "domain": f"{repo_dir}/examples/IPC_domains_propositional/driverlog/domain.pddl",
    "task": f"{repo_dir}/examples/IPC_domains_propositional/driverlog/prob15.pddl",
     "sas_file":"driverlog15.sas",
     "scope": True,
     "write_erfs":True
}

main_from_other_script(**tas_kwargs)
# print("\n".join(cmd_list))