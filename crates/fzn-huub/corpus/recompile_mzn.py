#!/usr/bin/env python3

import os
import subprocess
import tempfile
import urllib.request

from pathlib import Path

# Map of objects containing [model] key that points to the url where the model
# can be downloaded, and [instances] key that points to a map of
# [compiled file name] -> [instance data url].
INSTANCES = [
    {  # Amaze 3
        "model": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2014/amaze/amaze3.mzn",
        "instances": {
            "amaze3_2012_03_19.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2019/amaze/2012-03-19.dzn"
        },
    },
    {  # Jobshop
        "model": "https://gist.githubusercontent.com/Dekker1/6662819320b5741b57913813dfcc0afa/raw/11e882546aed599a33a7c9426a445b8d0ac986c7/jobshop_disj",
        "instances": {
            "jobshop_la01.fzn.json": "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/jobshop/jobshop_la01.dzn",
            "jobshop_la02.fzn.json": "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/jobshop/jobshop_la02.dzn",
            "jobshop_la03.fzn.json": "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/jobshop/jobshop_la03.dzn",
            "jobshop_la04.fzn.json": "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/jobshop/jobshop_la04.dzn",
            "jobshop_la05.fzn.json": "https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/jobshop/jobshop_la05.dzn",
            "jobshop_newspaper.fzn.json": "https://gist.githubusercontent.com/Dekker1/6662819320b5741b57913813dfcc0afa/raw/11e882546aed599a33a7c9426a445b8d0ac986c7/jobshop_newspaper.dzn",
        },
    },
    {  # Radiation
        "model": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2020/radiation/radiation.mzn",
        "instances": {
            "radiation_i6_9.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2020/radiation/i6-9.dzn",
            "radiation_i8_9.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2020/radiation/i8-9.dzn",
        },
    },
    {  # Steiner Systems
        "model": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2021/steiner-systems/steiner-systems.mzn",
        "instances": {
            "steiner_t3_k4_N8.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2021/steiner-systems/steiner_t3_k4_N8.json",
            "steiner_t6_k6_N7.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2021/steiner-systems/steiner_t6_k6_N7.json",
        },
    },
    {  # Sudoku Fixed
        "model": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2023/sudoku_fixed/sudoku_fixed.mzn",
        "instances": {
            "sudoku_p0.fzn.json": "http://www.hakank.org/minizinc/sudoku_problems2/sudoku_p0.dzn",
            "sudoku_p48.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2023/sudoku_fixed/sudoku_p48.dzn",
        },
    },
    {  # Stochastic VRP
        "model": None,
        "instances": {
            "svrp_s4_v2_c3.fzn.json": "https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2019/stochastic-vrp/vrp-s4-v2-c3_svrp-v2-c3_det.mzn"
        },
    },
    {  # Miscellaneous: instances constructed to test different parts of the solver
        "model": None,
        "instances": {
            "bool_indomain_max.fzn.json": "bool_indomain_max.mzn",
            "bool_indomain_min.fzn.json": "bool_indomain_min.mzn",
            "int_indomain_max_1.fzn.json": "int_indomain_max_1.mzn",
            "int_indomain_max_2.fzn.json": "int_indomain_max_2.mzn",
            "int_indomain_max_3.fzn.json": "int_indomain_max_3.mzn",
            "int_indomain_max_4.fzn.json": "int_indomain_max_4.mzn",
            "int_indomain_max_5.fzn.json": "int_indomain_max_5.mzn",
            "int_indomain_min_1.fzn.json": "int_indomain_min_1.mzn",
            "int_indomain_min_2.fzn.json": "int_indomain_min_2.mzn",
            "int_indomain_min_3.fzn.json": "int_indomain_min_3.mzn",
            "int_indomain_min_4.fzn.json": "int_indomain_min_4.mzn",
            "int_indomain_min_5.fzn.json": "int_indomain_min_5.mzn",
            "seq_search_1.fzn.json": "seq_search_1.mzn",
            "seq_search_2.fzn.json": "seq_search_2.mzn",
            "seq_search_3.fzn.json": "seq_search_3.mzn",
            "seq_search_4.fzn.json": "seq_search_4.mzn",
        },
    },
]


# Load the contents for a temporary file from a URL or a local file
def load_file(temp_file, url, base_path):
    if url is None:
        return
    if url.startswith("http"):
        with urllib.request.urlopen(url) as content:
            temp_file.write(content.read())
    else:
        local_file = base_path / url
        assert local_file.exists(), f"Local file not found: {local_file}"
        temp_file.write(local_file.read_bytes())
    temp_file.flush()


if __name__ == "__main__":
    this_dir = Path(os.path.dirname(os.path.realpath(__file__)))
    msc_file = (
        this_dir.parent.parent.parent / "share" / "minizinc" / "solvers" / "huub.msc"
    )
    assert msc_file.exists(), f"Solver configuration file not found: {msc_file}"

    for model in INSTANCES:
        with tempfile.NamedTemporaryFile(suffix="model.mzn") as model_file:
            load_file(model_file, model["model"], this_dir)

            for out_file, url in model["instances"].items():
                # Determine correct suffix for the "data" temporary file
                if url.endswith(".json"):
                    suffix = ".json"
                elif url.endswith(".mzn"):
                    suffix = ".mzn"
                else:
                    suffix = ".dzn"

                with tempfile.NamedTemporaryFile(
                    suffix="instance" + suffix
                ) as data_file:
                    load_file(data_file, url, this_dir)

                    out_path = this_dir / out_file
                    subprocess.run(
                        [
                            "minizinc",
                            "--compile",
                            "--solver",
                            str(msc_file),
                            "--output-objective",
                            "--output-fzn-to-file",
                            str(out_path),
                            model_file.name,
                            data_file.name,
                        ],
                        check=True,
                    )
