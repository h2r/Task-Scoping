import os, time, argparse, subprocess, json, shutil, re
import pandas as pd
import numpy as np
from oo_scoping.writeback_pddl import get_scoped_problem_path, get_scoped_domain_path

root_dir = os.path.dirname(os.path.dirname(__file__))

# Main function
def run_experiment(n_runs, domain, problem, log_dir, force_clear=False, planner='default', run_id=None):
    start_time_exp = time.time()
    log_dir = log_dir + "/" + planner + "/" + problem.split(".")[0]
    if run_id is None or run_id == -1:
        run_id_start = 0
    else:
        run_id_start = run_id

    if run_id != -1:
        # Clear log dir if force_clear is True
        # if force_clear and os.path.exists(log_dir):
        #     shutil.rmtree(log_dir)
        # Make the log directory. Throws an error if the directory already exists
        os.makedirs(log_dir, exist_ok=True)

    # Save arguments to log_dir
    args_dict = {
        "n_runs":n_runs,
        "domain":domain,
        "problem":problem,
        "log_dir":log_dir
    }
    with open(f"{log_dir}/args.json", "w") as f:
        json.dump({k: str(v) for k, v in args_dict.items()}, f)

    timings_dict = {
        "scope":[],
        "plan_scoped":[],
        "total_scoped_time":[],
        "plan_unscoped":[],
        "plan_length_scoped": [],
        "plan_length_unscoped": [],
        "expanded_nodes_scoped": [],
        "expanded_nodes_unscoped": [],
        "evaluated_states_scoped": [],
        "evaluated_states_unscoped": [],
    }

    # This would be more precise if we recorded time for multiple iterations of each portion, then divided. TODO consider doing this.
    for i_run in range(run_id_start, run_id_start + n_runs):
        print(f"Run {i_run}")
        log_dir_this_run = f"{log_dir}/{i_run}"
        timings_path = f"{log_dir_this_run}/times.json"

        if run_id != -1:
            if force_clear and os.path.exists(log_dir_this_run):
                shutil.rmtree(log_dir_this_run)
            os.makedirs(log_dir_this_run, exist_ok=False)
            # Scoping
            print("Scoping")
            scope_start = time.time()
            scope_cmd_output = scope(domain, problem)
            scope_end = time.time()
            if scope_cmd_output.returncode != 0:
                raise ValueError(f"Scoping failed with returncode {scope_cmd_output.returncode}\nstderr: {scope_cmd_output.stderr}\nstdout: {scope_cmd_output.stdout}")
            scope_time = scope_end - scope_start
            timings_dict["scope"].append(scope_time)
            with open(timings_path, "w") as f:
                json.dump(timings_dict, f)
            save_cmd_output(scope_cmd_output, f"{log_dir_this_run}/scope")

            # Planning on scoped
            print("Planning (scoped)")
            plan_scoped_start_time = time.time()
            problem_scoped_with_cl = get_scoped_problem_path(problem)#, suffix="with_cl")
            domain_scoped = get_scoped_domain_path(domain, problem)
            plan_scoped_cmd_output = plan(domain_scoped, problem_scoped_with_cl, planner=planner)
            if plan_scoped_cmd_output.returncode != 0:
                raise ValueError(f"Planning on scoped problem failed with returncode {plan_scoped_cmd_output.returncode}\nstderr: {plan_scoped_cmd_output.stderr}\nstdout: {plan_scoped_cmd_output.stdout}")
            plan_scoped_end_time = time.time()
            plan_scoped_time = plan_scoped_end_time - plan_scoped_start_time
            timings_dict["plan_scoped"].append(plan_scoped_time)
            timings_dict["total_scoped_time"].append(scope_time + plan_scoped_time)
            timings_dict["plan_length_scoped"].append(int(re.search(r"(Plan-Length:)(?! )\d*", plan_scoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            timings_dict["expanded_nodes_scoped"].append(int(re.search(r"(Expanded Nodes:)(?! )\d*", plan_scoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            timings_dict["evaluated_states_scoped"].append(int(re.search(r"(States Evaluated:)(?! )\d*", plan_scoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            with open(timings_path, "w") as f:
                json.dump(timings_dict, f)
            save_cmd_output(plan_scoped_cmd_output, f"{log_dir_this_run}/plan_scoped")

            # Planning on unscoped
            print("Planning (unscoped)")
            plan_unscoped_start_time = time.time()
            plan_unscoped_cmd_output = plan(domain, problem, planner=planner)
            plan_unscoped_end_time = time.time()
            if plan_unscoped_cmd_output.returncode != 0:
                raise ValueError(f"Planning on unscoped problem failed with returncode {plan_unscoped_cmd_output.returncode}\nstderr: {plan_unscoped_cmd_output.stderr}\nstdout: {plan_unscoped_cmd_output.stdout}")
            timings_dict["plan_unscoped"].append(plan_unscoped_end_time - plan_unscoped_start_time)
            timings_dict["plan_length_unscoped"].append(int(re.search(r"(Plan-Length:)(?! )\d*", plan_unscoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            timings_dict["expanded_nodes_unscoped"].append(int(re.search(r"(Expanded Nodes:)(?! )\d*", plan_unscoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            timings_dict["evaluated_states_unscoped"].append(int(re.search(r"(States Evaluated:)(?! )\d*", plan_unscoped_cmd_output.stdout.decode()).group().split(':')[-1]))
            with open(timings_path, "w") as f:
                json.dump(timings_dict, f)
            save_cmd_output(plan_unscoped_cmd_output, f"{log_dir_this_run}/plan_unscoped")
        else:
            print("Loading results")
            with open(timings_path, "r") as f:
                loaded_timings = json.load(f)
                for key in loaded_timings.keys():
                    value = np.nan if loaded_timings[key] == [] else loaded_timings[key][0]
                    timings_dict[key].append(value)

    end_time_exp = time.time()
    experiment_duration = end_time_exp - start_time_exp
    print(f"Finished experiment")
    print(f"Ran {n_runs} trials for a total duration of {experiment_duration}")
    # print(timings_dict)
    df_times = pd.DataFrame(data=timings_dict)
    s_times_avg = df_times.mean()
    s_times_avg.name = 'avg'
    s_times_std = df_times.std()
    s_times_std.name = 'std'
    s_times_cv = s_times_std / s_times_avg
    s_times_cv.name = "cv"
    df_time_summary = pd.concat([s_times_avg, s_times_std, s_times_cv], axis=1)
    print(f"Timing summary:")
    print(df_time_summary)
    if n_runs > 1:
        df_time_summary.to_csv(f"{log_dir}/timing_summary.csv", index=True)

def save_cmd_output(cmd_output, save_dir):
    os.makedirs(save_dir, exist_ok=False)
    outpaths = {
        "args":f"{save_dir}/args.txt",
        "stdout":f"{save_dir}/stdout.txt",
        "stderr":f"{save_dir}/stderr.txt",
        "returncode":f"{save_dir}/returncode.txt"
    }

    with open(outpaths["args"], "w") as f:
        # TODO would be better to store as a csv perhaps
        f.write(str(cmd_output.args))

    with open(outpaths["stdout"], "w") as f:
        f.write(cmd_output.stdout.decode('UTF-8'))

    with open(outpaths["stderr"], "w") as f:
        f.write(cmd_output.stderr.decode('UTF-8'))

    with open(outpaths["returncode"], "w") as f:
        f.write(str(cmd_output.returncode))

    return outpaths



def scope(domain, problem):
    scope_script_pth =  f"{root_dir}/oo_scoping/scope_and_writeback_pddl.py"
    assert os.path.isfile(scope_script_pth)
    cmd_pieces =["python", scope_script_pth, "--domain", domain, "--prob", problem]
    cmd_output = subprocess.run(cmd_pieces, capture_output=True, shell=False)
    return cmd_output



def plan(domain, problem, planner='default'):
    if planner=='opt':
        cmd_pieces = ["./enhsp-2020.sif", "--domain", domain, "--problem", problem, '-s', 'WAStar', '-h', 'hrmax', '-ties', 'larger_g']
    elif planner=='sat':
        cmd_pieces = ["./enhsp-2020.sif", "--domain", domain, "--problem", problem, '-s', 'gbfs', '-h', 'hadd', '-ties', 'arbitrary']
    else:
        if planner != 'default':
            raise ValueError('Unknown planner type')
        cmd_pieces = ["./enhsp-2020.sif", "--domain", domain, "--problem", problem, '-s', 'WAStar', '-h', 'aibr', '-ties', 'arbitrary']
    cmd_output = subprocess.run(" ".join(cmd_pieces), capture_output=True, shell=True)
    return cmd_output


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("n_runs" ,type=int)
    parser.add_argument("domain", type=str)
    parser.add_argument("problem", type=str)
    parser.add_argument("log_dir", type=str)
    parser.add_argument("--force_clear_log_dir", default=False, action='store_true')
    parser.add_argument("--planner", type=str, default='default', choices=['default', 'sat', 'opt'])
    parser.add_argument("--run_id", type=int, default=None)

    args = parser.parse_args()

    run_experiment(args.n_runs, args.domain, args.problem, args.log_dir, args.force_clear_log_dir, args.planner, args.run_id)
