import subprocess, os
from typing import Optional, Iterable

def translate(domain, problem, sas_path) -> subprocess.CompletedProcess[bytes]:
    cmd_pieces = ["python", "downward_translate/translate_and_scope.py", domain, problem, "--sas-file", sas_path]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output


def translate_and_scope(domain: str, problem: str, unscoped_sas_path: str) -> subprocess.CompletedProcess[bytes]:
    cmd_pieces = ["python", "downward_translate/translate_and_scope.py", domain, problem, "--sas-file", unscoped_sas_path, "--scope", "True"]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output

def plan(sas_path: str, fd_path: Optional[str] = None, config_args: Iterable = ("--alias", "seq-opt-lmcut")) -> subprocess.CompletedProcess[bytes]:
    # Try to load fd_path from env variable if it is unspecified
    if fd_path is None:
        fd_path = os.getenv("FD_PATH")
        if fd_path is None:
            raise ValueError("Please either specify fd_path or set the env variable FD_PATH")
    config_args = list(config_args)
    cmd_pieces = ["python", fd_path, "--search"] + config_args + [sas_path]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output
