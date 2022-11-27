import os, time, argparse, subprocess, json, shutil, glob
import pandas as pd
"""
TODO:
Get state-visited counts
Use https://gist.github.com/nawatts/e2cdca610463200c12eac2a14efc0bfb to print output
"""

# Helper functions
def get_scoped_file_path(unscoped_file):
    return add_path_suffix(unscoped_file, "_scoped")

def add_path_suffix(p, s):
    basename, ext = os.path.splitext(p)
    return basename + s + ext

# def dir_path(path):
#     if os.path.isdir(path):
#         return path
#     else:
#         raise argparse.ArgumentTypeError(f"readable_dir:{path} is not a valid path")

# Main function
def run_experiment(n_runs, domain, problem, fd_path, log_dir, force_clear=False):
    start_time_exp = time.time()
    # Clear log dir if force_clear is True
    if force_clear and os.path.exists(log_dir):
        shutil.rmtree(log_dir)
    # Make the log directory. Throws an error if the directory already exists
    os.makedirs(log_dir, exist_ok=False)
    # Save arguments to log_dir
    args_dict = {
        "n_runs":n_runs,
        "domain":domain,
        "problem":problem,
        "fd_path":fd_path,
        "log_dir":log_dir
    }
    with open(f"{log_dir}/args.json", "w") as f:
        json.dump({k: str(v) for k, v in args_dict.items()}, f)

    timings_dict = {
        "translate":[],
        "translate_and_scope":[],
        "plan_unscoped":[],
        "plan_scoped":[]
    }
    timings_path = f"{log_dir}/times.json"
    # This would be more precise if we recorded time for multiple iterations of each portion, then divided. TODO consider doing this.
    for i_run in range(n_runs):
        log_dir_this_run = f"{log_dir}/{i_run}"
        os.makedirs(log_dir_this_run)
        print(f"Run {i_run}")
        # Translation
        print("Translating")
        sas_path = f"{log_dir_this_run}/unscoped.sas"

        # new_irrel_prob_file_name = f"{log_dir_this_run}/irrel.pddl"
        # add_irrel_goals_to_prob_file(domain, problem, new_irrel_prob_file_name)
        # problem = new_irrel_prob_file_name

        translate_start = time.time()
        trans_cmd_output = translate(domain, problem, sas_path)
        translate_end = time.time()
        if trans_cmd_output.returncode != 0:
                    raise ValueError(f"Translation failed with returncode {trans_cmd_output.returncode}\nstderr: {trans_cmd_output.stderr}\nstdout: {trans_cmd_output.stdout}")

        timings_dict["translate"].append(translate_end - translate_start)
        with open(timings_path, "w") as f:
            json.dump(timings_dict, f)
        save_cmd_output(trans_cmd_output, f"{log_dir_this_run}/translate")

        # Scoping
        print("Scoping")
        sas_2_path = f"{log_dir_this_run}/unscoped2.sas"
        sas_scoped_path = get_scoped_file_path(sas_2_path)
        translate_and_scope_start = time.time()
        scope_cmd_output = translate_and_scope(domain, problem, sas_2_path)
        translate_and_scope_end = time.time()
        if scope_cmd_output.returncode != 0:
            raise ValueError(f"Scoping failed with returncode {scope_cmd_output.returncode}\nstderr: {scope_cmd_output.stderr}\nstdout: {scope_cmd_output.stdout}")

        timings_dict["translate_and_scope"].append(translate_and_scope_end - translate_and_scope_start)
        with open(timings_path, "w") as f:
            json.dump(timings_dict, f)
        save_cmd_output(scope_cmd_output, f"{log_dir_this_run}/translate_and_scope")

        # Planning on unscoped
        print("Planning on unscoped")
        plan_unscoped_start_time = time.time()
        plan_unscoped_cmd_output = plan(sas_2_path, fd_path)
        plan_unscoped_end_time = time.time()
        if plan_unscoped_cmd_output.returncode != 0:
            raise ValueError(f"Planning on unscoped problem failed with returncode {plan_unscoped_cmd_output.returncode}\nstderr: {plan_unscoped_cmd_output.stderr}\nstdout: {plan_unscoped_cmd_output.stdout}")

        timings_dict["plan_unscoped"].append(plan_unscoped_end_time - plan_unscoped_start_time)
        with open(timings_path, "w") as f:
            json.dump(timings_dict, f)
        save_cmd_output(plan_unscoped_cmd_output, f"{log_dir_this_run}/plan_unscoped")

        # Planning on scoped
        print("Planning on scoped")
        plan_scoped_start_time = time.time()
        plan_scoped_cmd_output = plan(sas_scoped_path, fd_path)
        plan_scoped_end_time = time.time()
        if plan_scoped_cmd_output.returncode != 0:
            raise ValueError(f"Planning on scoped problem failed with returncode {plan_scoped_cmd_output.returncode}\nstderr: {plan_scoped_cmd_output.stderr}\nstdout: {plan_scoped_cmd_output.stdout}")
        timings_dict["plan_scoped"].append(plan_scoped_end_time - plan_scoped_start_time)
        save_cmd_output(plan_scoped_cmd_output, f"{log_dir_this_run}/plan_scoped")
    end_time_exp = time.time()
    experiment_duration = end_time_exp - start_time_exp
    print(f"Finished experiment")
    print(f"Ran {n_runs} trials for a total duration of {experiment_duration}")
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
    df_time_summary.to_csv(f"{log_dir}/timing_summary.csv", index=True)
    return timings_dict


def run_experiments_on_folder(n_runs, domain, problem_folder, fd_path, log_dir, force_clear=False):
    total_timings_dict = {}
    num_solved_problems = 0
    problem_files = glob.glob(problem_folder + "*")

    for problem in problem_files:
        log_dir_this_problem = log_dir + "/" + problem.split(".")[-2]
        
        try:
            curr_timings_dict = run_experiment(n_runs, domain, problem, fd_path, log_dir_this_problem, force_clear)
        except ValueError:
            # In this case, the randomly-generated problem was impossible to solve.
            # Simply skip and move on.
            print(f"Problem {problem} is impossible to solve.")
            continue
        
        num_solved_problems += 1
        if len(total_timings_dict) == 0:
            total_timings_dict = curr_timings_dict
        else:
            for key in total_timings_dict.keys():
                total_timings_dict[key] += curr_timings_dict[key]
        
        # Convert timings dict to dataframe for easy processing (code mostly
        # copied from above method).
        df_times = pd.DataFrame(data=total_timings_dict)
        s_times_avg = df_times.mean()
        s_times_avg.name = 'avg'
        s_times_std = df_times.std()
        s_times_std.name = 'std'
        s_times_cv = s_times_std / s_times_avg
        s_times_cv.name = "cv"
        df_time_summary = pd.concat([s_times_avg, s_times_std, s_times_cv], axis=1)

        print(f"Finished experiments; {num_solved_problems} problems out of {len(problem_files)} were solvable.")
        print(f"Aggregate Timing summary:")
        print(df_time_summary)
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("n_runs" ,type=int)
    parser.add_argument("domain", type=str)
    parser.add_argument("problem", type=str)
    parser.add_argument("fd_path", type=str)
    parser.add_argument("log_dir", type=str)
    parser.add_argument("--force_clear_log_dir", default=False, action='store_true')
    parser.add_argument("--problems_dir", type=str, required=False, default=None)

    args = parser.parse_args()

    if args.problems_dir is None:
        run_experiment(args.n_runs, args.domain, args.problem, args.fd_path, args.log_dir, args.force_clear_log_dir)
    else:
        run_experiments_on_folder(args.n_runs, args.domain, args.problems_dir, args.fd_path, args.log_dir, args.force_clear_log_dir)
