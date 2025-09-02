# Huub's MiniZinc testing and benchmarking corpus

This folder contains a collection of (compiled) MiniZinc instances that are used as part of the `flatzinc_tests` integration test target (included in `cargo test`) and the `fzn_huub_bench` benchmarking target (included in `cargo bench`).
The instances are collected from various sources, such the MiniZinc benchmarks and challenge repositories, and some of the instances are hand-crafted to test specific features or regressions in the Huub solver.

## Recompiling the MiniZinc instances

If the MiniZinc library that is distributed with Huub is updated, the MiniZinc instances in this folder need to be recompiled.
This can be done by running the `recompile_mzn.py` script in this folder.
To run this script, you need to have an (up-to-date) version of the MiniZinc compiler installed on your system.
This script will temporarily download foreign MiniZinc instances, compile them with the (updated) Huub MiniZinc library, and override the compiled instances in this folder.

## List of Foreign MiniZinc instances

For foreign models included in the testing infrastructure, the following list contains links to the original models, and the file name of the compiled instances with links to the associated data file.

- [Amaze 3](https://github.com/MiniZinc/mzn-challenge/blob/develop/2014/amaze/amaze3.mzn)
  - `amaze3_2012_03_19.fzn.json` - [mod2012-03-19.dzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2019/amaze/2012-03-19.dzn)
- [RCPSP](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/rcpsp/rcpsp.mzn)
  - `rcpsp_01.fzn.json` - [01.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/rcpsp/01.dzn)
  - `rcpsp_02.fzn.json` - [02.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/rcpsp/02.dzn)
  - `rcpsp_03.fzn.json` - [03.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/rcpsp/03.dzn)
- [MRCPSP](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/mrcpsp/mrcpsp.mzn)
  - `mrcpsp_j10_10_1.fzn.json` - [j10_10_1.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/mrcpsp/mm_j10/j10_10_1.dzn)
  - `mrcpsp_j10_10_2.fzn.json` - [j10_10_2.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/mrcpsp/mm_j10/j10_10_2.dzn)
  - `mrcpsp_j10_10_3.fzn.json` - [j10_10_3.dzn](https://raw.githubusercontent.com/MiniZinc/minizinc-benchmarks/refs/heads/master/mrcpsp/mm_j10/j10_10_3.dzn)
- [Jobshop](https://github.com/MiniZinc/minizinc-benchmarks/blob/master/jobshop/jobshop.mzn) (adapted to use disjunctive global constraint)
  - `jobshop_la02.fzn.json` - [jobshop_la02.dzn](https://github.com/MiniZinc/minizinc-benchmarks/blob/master/jobshop/jobshop_la02.dzn)
  - `jobshop_la03.fzn.json` - [jobshop_la03.dzn](https://github.com/MiniZinc/minizinc-benchmarks/blob/master/jobshop/jobshop_la03.dzn)
  - `jobshop_la04.fzn.json` - [jobshop_la04.dzn](https://github.com/MiniZinc/minizinc-benchmarks/blob/master/jobshop/jobshop_la04.dzn)
  - `jobshop_la05.fzn.json` - [jobshop_la05.dzn](https://github.com/MiniZinc/minizinc-benchmarks/blob/master/jobshop/jobshop_la05.dzn)
  - `jobshop_newspaper.fzn.json` - [jobshop_newspaper.dzn](https://github.com/hakank/hakank/blob/master/minizinc/jobshop_newspaper.dzn) (adapted to fit model)
- [Kidney Exchange](https://github.com/MiniZinc/mzn-challenge/blob/develop/2023/kidney-exchange/ccmcp.mzn)
	- `ccmcp_3_20_0.fzn.json` - [3_20_0.15_3.dzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2023/kidney-exchange/3_20_0.15_3.dzn)
- [(Generalized) Peacable Queens](https://github.com/MiniZinc/mzn-challenge/blob/develop/2022/generalized-peacable-queens/peaceable_queens.mzn)
  - `peaceable_queens_n5_q3.fzn.json` - [n8_q3.json](./peaceable_queens_n5_q3.json)
- [Portal](https://github.com/MiniZinc/mzn-challenge/blob/develop/2024/portal/portal.mzn)
  -  `portal_10_9_10.fzn.json` - [random_10_9_10.json](https://raw.githubusercontent.com/MiniZinc/mzn-challenge/refs/heads/develop/2024/portal/random_10_9_10.json)
- [Radiation](https://github.com/MiniZinc/mzn-challenge/blob/develop/2020/radiation/radiation.mzn)
  - `radiation_i6_9.fzn.json` - [i6_9.dzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2020/radiation/i6-9.dzn)
  - `radiation_i8_9.fzn.json` - [i8_9.dzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2020/radiation/i8-9.dzn)
- [Steiner Systems](https://github.com/MiniZinc/mzn-challenge/blob/develop/2021/steiner-systems/steiner-systems.mzn)
  - `steiner_t3_k4_N8.fzn.json` - [t3_k4_N8.json](https://github.com/MiniZinc/mzn-challenge/blob/develop/2021/steiner-systems/steiner_t3_k4_N8.json)
  - `steiner_t6_k6_N7.fzn.json` - [t6_k6_N7.json](https://github.com/MiniZinc/mzn-challenge/blob/develop/2021/steiner-systems/steiner_t6_k6_N7.json)
- [Sudoku Fixed](https://github.com/MiniZinc/mzn-challenge/blob/develop/2023/sudoku_fixed/sudoku_fixed.mzn)
  - `sudoku_p0.fzn.json` - [sudoku_p0.dzn](http://www.hakank.org/minizinc/sudoku_problems2/sudoku_p0.dzn)
  - `sudoku_p48.fzn.json` - [sudoku_p48.dzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2023/sudoku_fixed/sudoku_p48.dzn)
- Stochastic VRP (no shared model between instances)
  - `svrp_s4_v2_c3.fzn.json` - [vrp-s4-v2-c3_svrp-v2-c3_det.mzn](https://github.com/MiniZinc/mzn-challenge/blob/develop/2019/stochastic-vrp/vrp-s4-v2-c3_svrp-v2-c3_det.mzn)
