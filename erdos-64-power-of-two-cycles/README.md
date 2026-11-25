# Erdős Problem #64 for graphs forbidding an induced path and an isolated vertex

**Theorem.** Every nonempty simple graph of minimum degree at least three with no induced copy of $P_{14} \sqcup K_1$ contains a simple cycle of length 4, 8, or 16. Here $P_{14}$ is the path on fourteen vertices. The extra vertex has no neighbor on the path.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #64, the Erdős–Gyárfás conjecture on cycles of power-of-two length. [Problem statement](https://www.erdosproblems.com/64) |
| Status | Proved for graphs forbidding an induced $P_{14} \sqcup K_1$, including all $P_{14}$-free graphs. The unrestricted finite-graph conjecture remains open. |
| Main theorems | `Erdos64.cycle_of_P14_plus_isolate_free` gives the three lengths. `Erdos64.power_of_two_cycle_of_P14_plus_isolate_free` gives the explicit power-of-two conclusion. [Erdos64.lean](Erdos64.lean) |
| Verification | `lake build` with Lean 4.36.0 and the standard library. Two finite computations in the main proof use `native_decide`. |
| Prior art | Checked 25 November 2026. Hegde, Sandeep and Shashank proved the $P_{13}$-free case. [Prior-art audit](../PRIOR_ART.md#erdős-64-power-of-two-cycles) |

## Proof

Suppose there is no cycle of length 4, 8, or 16. Two computer-checked lemmas apply.

1. The graph contains an induced $P_{14}$. [Erdos64.cycle_of_P14_free](Erdos64/PathFree.lean)
2. No such path dominates the graph. A path dominates if every vertex outside it has a neighbor on it. [Erdos64.cycle_of_dominatingP14](Erdos64/DominatingCases.lean)

Choose the path from the first lemma. By the second, some outside vertex has no neighbor on the path. That vertex and the path induce the forbidden $P_{14} \sqcup K_1$. ∎

For the first lemma, start with an edge. For each $r$ from 2 through 13, the search rules out a graph that contains an induced $P_r$ and has no induced $P_{r+1}$. For the second, the search starts with a dominating induced $P_{14}$.

Both searches expose one vertex at a time. An exposed vertex with at most two exposed neighbors must have a fresh neighbor. The search enumerates which exposed vertices could be adjacent to that new vertex. If two of them are the endpoints of a simple path of 2, 6, or 14 edges, the new vertex closes a cycle of length 4, 8, or 16. Exhausting these local choices covers host graphs of arbitrary order. [Longest-path search](Erdos64/PathFreeSearch.lean) · [Dominating-path search](Erdos64/Search.lean)

## Build and reproduce

From this directory, run

```sh
lake build
```

Lean proves that all possible neighborhoods are covered and that each rule used to discard a case is sound. The two finite evaluations use `native_decide`, which trusts Lean’s compiler for their Boolean results. The independent C++23 checker can be run separately. [Checker source](scripts/pfree_check.cpp)

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror scripts/pfree_check.cpp -o /tmp/erdos64-pfree-check
/tmp/erdos64-pfree-check
```

Expect 525,217 partial graphs across the twelve longest-path cases and 121,786 for the dominating-path case. The checker exits unsuccessfully if any branch remains unresolved.

The package also includes an elementary proof that forbidding both an induced net and an induced once-subdivided claw forces a 4-cycle at minimum degree three. Its endpoint is `Erdos64.NetAndTripod.fourCycle_of_netFree_subdividedClawFree`. [Elementary proof](Erdos64/NetAndTripod.lean)

## References

* [Erdős Problem #64](https://www.erdosproblems.com/64)
* [Hegde, Sandeep and Shashank, *Erdős–Gyárfás conjecture on graphs without long induced paths*](https://arxiv.org/abs/2410.22842)
* [Ducoffe and Dumitru, *Towards a more structured search for Erdős–Gyárfás counter-examples*](https://arxiv.org/abs/2609.28594)
