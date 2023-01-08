import subprocess

def translate(domain, problem, sas_path):
    cmd_pieces = ["python", "downward_translate/translate_and_scope.py", domain, problem, "--sas-file", sas_path]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output


def translate_and_scope(domain, problem, unscoped_sas_path):
    cmd_pieces = ["python", "downward_translate/translate_and_scope.py", domain, problem, "--sas-file", unscoped_sas_path, "--scope", "True"]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output

def plan(sas_path, fd_path):
    cmd_pieces = ["python", fd_path, "--alias", "seq-opt-lmcut", sas_path]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output
