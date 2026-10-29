# Hochbaum's Pseudoflow (HPF) Algorithm for (2-Piecewise Linear) Fully Parametric Minimum Cut
This package provides a fully parametric implementation of Hochbaum's Pseudoflow algorithm for minimum cut on directed graphs. In the parametric minimum cut problem, the capacity of source-adjacent arcs is monotone non-decreasing in the parameter `lambda` whereas the capacity of sink-adjacent arcs is monotone non-increasing in `lambda`. This solver requires that the capacities of source and sink adjacent arcs are 2-piecewise linear in `lambda`: `capacity = max(0, constant + multiplier * lambda)`.

This fully parametric solver finds the optimal minimum cut for all `lambda` values in a given range. The solution for all lambda values is represented with `O(n)` intervals for the parameter lambda. In each interval, the optimal minimum cut remains the same.

A simple parametric minimum cut solver that provides the optimal minimum cut for a given list of arc capacities is available [here](https://riot.ieor.berkeley.edu/Applications/Pseudoflow/parametric.html), and a non-parametric maximum flow version of pseudoflow is available [here](https://riot.ieor.berkeley.edu/Applications/Pseudoflow/maxflow.html).

This implementation uses a variant of the fully parametric HPF algorithm as described in:
>    DS Hochbaum (2008), The Pseudoflow algorithm: A new algorithm for the maximum flow problem. Operations Research, 58(4):992-1009.

This implementation does not use *free runs* nor does it carry flows and labels between runs (see pg.15). This implementation should therefore **not be used** for comparison with the fully parametric HPF algorithm.

## Instructions for C
Navigate to directory `src/pseudoflow/c`, and compile the `hpf` executable with `make`.

To execute the solver, use:
```bash
hpf input-file.txt output-file.txt
```

The input file should contain the graph structure and is assumed to have the following format:
```
    c <comment lines>
    p <# nodes> <# arcs> <lower bound> <upper bound>
    n <source node> s
    n <sink node> t
    a <from-node> <to-node> <constant capacity> <lambda multiplier>
```
where the `a` line is repeated for each arc. The file should satisfy the following conditions:
- Nodes are labeled `0 .. <# nodes> - 1`.
- `<lambda multiplier>` is non-negative if `<from-node> == <source node>` and `<to-node> != <sink-node>`.
- `<lambda multiplier>` is non-positive if `<from-node> != <source node>` and `<to-node> == <sink-node>`.
- `<lambda multiplier>` is zero if `<from-node> != <source node>` and `<to-node> != <sink-node>`.

The solver will generate the following output file:
```
t <time (in sec) read data> <time (in sec) initialize> <time (in sec) solve>
s <# arc scans> <# mergers> <# pushes> <# relabels> <# gaps>
p <number of breakpoints = k>
l <lambda> <node> <node> ...
```
The `l` line appears for each breakpoint, in increasing order of `lambda`, and lists the nodes that are added into the source set at that `lambda` value.

See `src/pseudoflow/c/example` for an example.
