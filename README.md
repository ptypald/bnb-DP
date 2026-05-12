# Branch-and-bound / dynamic-programming path planning

This repository contains research code associated with the paper:

> Panagiotis Typaldos, Markos Papageorgiou, and Ioannis Papamichail,  
> "Optimization-based path-planning for connected and non-connected automated vehicles,"  
> *Transportation Research Part C: Emerging Technologies*, 134, 103487, 2022.  
> DOI: 10.1016/j.trc.2021.103487

The code studies discrete path-planning strategies for automated vehicles moving in multilane traffic with surrounding vehicles represented through prescribed trajectories. The repository includes:

- a dynamic-programming solver in `main-dp.c`
- a branch-and-bound / DFS planner in `main-bnb-dp.c`
- a compact executable scenario in `input.txt`
- a committed example visualization payload in `viz/data/data.js`
- a browser-based trajectory visualizer under `viz/`

## Repository map

| Path | Purpose |
| --- | --- |
| `main-dp.c` | Dynamic-programming planner that reads a scenario from standard input and emits visualizer-ready trajectory data on standard output |
| `main-bnb-dp.c` | Branch-and-bound / DFS planner that reads a scenario and writes `viz/data/data.js` |
| `input.txt` | Compact sample scenario |
| `viz/visualize-v3.html` | Browser visualizer for generated trajectories |

## Build

The repository uses plain C and the system math library.

```bash
make
```

This produces:

- `build/bnb_dp`
- `build/bnb_dfs`

To clean local binaries:

```bash
make clean
```

## Run the dynamic-programming solver

```bash
./build/bnb_dp < input.txt > /tmp/bnb_dp_data.js
```

The solver prints trajectory data in the JavaScript object format expected by the visualizer. To inspect a generated trajectory in the bundled visualization page, place the output at:

```bash
viz/data/data.js
```

and open:

```text
viz/visualize-v3.html
```

## Run the branch-and-bound / DFS prototype

```bash
./build/bnb_dfs < input.txt
```

This prototype writes its visualizer payload directly to:

```text
viz/data/data.js
```

It also reports runtime information in the terminal.

## Input format

Scenario files are line-oriented text files with entries such as:

```text
"vd":20.0
"numlanes":3
"numsteps":15
"T":1.0
"x(0)":30.0
"y(0)":0
"v(0)":12
"obst_x(0,0)":50
"obst_y(0,0)":0
"obst_v(0,0)":10
```

The planners parse vehicle, roadway, and obstacle parameters from standard input.

## Visualizer

The `viz/` folder contains a browser visualizer for ego and obstacle trajectories. The committed `viz/data/data.js` file serves as a ready-to-open example payload, while solver outputs can replace it for new runs.

## Notes for reuse

- The code is research-oriented and organized to preserve the original experimental workflow.
- `main-dp.c` is the cleaner entry point for dynamic-programming experiments.
- `main-bnb-dp.c` is useful for understanding the tree-search / branch-and-bound variant represented in the paper lineage.

## Citation

If you use this code or build on it, please cite the article above. A machine-readable citation file is included in [`CITATION.cff`](./CITATION.cff).
