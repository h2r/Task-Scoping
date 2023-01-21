import re, os
from typing import Tuple
import pandas as pd

results_path_fd = f"{os.path.dirname(__file__)}/ignore/results-summaries/fd"
results_path_enhsp = f"{os.path.dirname(__file__)}/ignore/results-summaries/enhsp"
summaries_dir = f"{os.path.dirname(__file__)}/ignore/"



prob_name_pat = "(prob\S+):"


class ResultParser:
    def __init__(self, s: str) -> None:
        self.s = s
        self.lines = [x.strip() for x in self.s.splitlines()]
        self.i = 0
        self.x = set()
    
    def parse(self):
        # # Config
        # pat_planner = "\s+-\s+(?P<planner>\w+)\s+(?P<planner_config>\(\w+\))"
        # m_planner = re.match(pat_planner, self.lines[1])
        # Post config
        self.i = 4
        finished = False
        dfs = []
        while not finished:
            if self.i in self.x:
                # raise ValueError(str(self.i))
                print("oof")
            self.x.add(self.i)
            if self.i >= len(self.lines):
                finished = True
                break
            if self.lines[self.i] == "":
                self.i += 1

            if re.match(prob_name_pat, self.lines[self.i]):
                dfs.append(self.parse_problem_chunk())
        
        df = pd.concat(dfs)
        # df["planner"] = m_planner.group("planner")
        # df["planner_config"] = m_planner.group("planner_config")
        df["domain"] = self.lines[0]
        return df


    def parse_problem_chunk(self) -> pd.DataFrame:
        nm = re.match(prob_name_pat,self.lines[self.i]).group()
        self.i += 1
        in_problem_chunk = True
        # skip header
        self.i += 1
        # parse rows
        rows = []
        while in_problem_chunk:
            if self.i in self.x:
                raise ValueError(str(self.i))
            self.x.add(self.i)
            if self.i >= len(self.lines):
                in_problem_chunk = False
                self.i += 1
                break
            s = self.lines[self.i]
            if s == "":
                in_problem_chunk = False
            else:
                pieces = re.split("\s+", s)
                if len(pieces) == 4:
                    pieces.append("")
                else:
                    notes = " ".join(pieces[4:])
                    pieces = pieces[:4] + [notes]
                rows.append(pieces)
            self.i += 1

        df = pd.DataFrame(data=rows, columns=["metric", "avg", "std", "cv", "notes"])
        df["prob_name"] = nm
        return df

def parse_all_results(d: str) -> pd.DataFrame:
    nms = [x for x in os.listdir(d) if os.path.isfile(f"{d}/{x}")]
    dfs = []
    for nm in nms:
        pth = f"{d}/{nm}"
        print("Parsing:")
        print(pth)
        planner, config, domain = nm.split(".txt")[0].split("-")
        with open(pth, "r") as f:
            s = f.read()
        df = ResultParser(s).parse()
        df["planner"] = planner
        df["config"] = config
        df["domain"] = domain
        dfs.append(df)
    return pd.concat(dfs)



if __name__ == "__main__":
    df_fd = parse_all_results(results_path_fd)
    print(df_fd)
    df_fd.to_csv(f"{summaries_dir}/fd_summary.csv", index=False)
    # df_enhsp = parse_all_results(results_path_enhsp)
    # print(df_enhsp)
    # df_enhsp.to_csv(f"{summaries_dir}/enhsp_summary.csv", index=False)
