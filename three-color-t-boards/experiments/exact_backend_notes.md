# Independent exact counting backend: d4

The official CRIL **d4** counter reproduced all four solved validation counts, while neither unrestricted ternary run finished. Both full runs hit their 120-second wall limits with exit status 124 and record `null` (not zero). No approximate mode, partial count, or third full run was used.

## Source and arithmetic

We used <https://github.com/crillab/d4> pinned to commit `333370cc1e843dd0749c1efe88516e72b5239174` (2023-05-17), choosing its standalone CLI over the newer `crillab/d4v2` library-plus-demo repo.

Unlike Ganak, d4 is a separate DPLL/knowledge-compilation counter with its own component cache, a MiniSAT-derived SAT engine, and PaToH partitioning. We built it locally against installed GMP and zlib, extracting missing Boost 1.83 headers from a Debian development package into `exact_backend_tools/boost` without modifying system directories.

Counting uses **arbitrary-precision integers**, never rounded floats. Unweighted input literals get weight 1 in [`ParserProblem.cc`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/manager/ParserProblem.cc#L56), and [`core/Main.cc`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/core/Main.cc#L279) instantiates `ModelCounter<mpz_int>`. All six logs confirm `Integer mode` (the `precision` flag only affects floating-weight runs).

Caching is exact rather than probabilistic: before accepting a cache hit, d4 checks the serialized component header and runs `memcmp` over the full component data ([`CacheCNFManager.hh`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/manager/CacheCNFManager.hh#L172)). We fixed the SAT seed to `91648253`, kept random branching at 0, and left the upstream PaToH seed at 1.

All runs count **every CNF variable**, passing no projection file (d4 ignores `c ind` comments). Because all auxiliary variables are uniquely forced by the board cells, full-variable model counting equals board counting. Full ternary formulas include orbit breaking, so a finished count would multiply by 12 to give all labeled boards, though no full run finished.

## Diagnostic change and options

`exact_backend_trace.patch` adds logging only: periodic stats every 256 recursive calls, plus branch traces for the first 32 decisions and then powers of two. Search, simplification, caching, and arithmetic stay unchanged. All hashes (source, binary, patch, PaToH archive, Boost package), compiler info, and linked libraries are saved in `exact_backend_provenance.json`.

Every run used:

```text
-mc -ph=TRUE -rnd-seed=91648253
```

Defaults keep VSADS scoring, clause-bipartite partitioning, graph reduction, equivalence probing, component splitting, and caching. In d4's source, `-ph=TRUE` (with reverse polarity off) branches on negative literals first, as confirmed by the traces, so search initially follows the all-false witness of each rephased CNF.

## Completed validations and bounded full runs

| Input | Terminal result | CPU seconds | Wall seconds | Peak RSS, KB |
| --- | ---: | ---: | ---: | ---: |
| Binary, unrestricted | 168 | 0.213 | 0.269 | 49,752 |
| Binary, orbit normalized | 42 | 0.123 | 0.216 | 49,752 |
| Fully fixed valid ternary board | 1 | 0.036 | 0.050 | 62,168 |
| Published ternary prefix C | 2 | 9.392 | 11.171 | 51,632 |
| Full ternary baseline | timeout; no count | 96.546 | 120.041 | 611,220 |
| Full ternary comparison encoding | timeout; no count | 81.322 | 120.074 | 125,600 |

CPU (user + system) and peak RSS come from the wrapper's `os.wait4`. In this release, [`cpuTime()`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/utils/System.hh#L74) calls `gettimeofday`, so both d4's reported time and the trace's `cpu` field actually measure **elapsed wall time** (stored as `solver_elapsed_seconds` in our parsed JSON), while d4's memory figure reports `VmPeak` rather than resident memory. Using OS counters avoids both pitfalls.

Prefix C finished in 55 recursive calls, 27 decisions, and 1 partitioner call, with no component splits and no cache hits. This confirms the count of 2 independently without implying d4 beats Ganak in general.

In **both full ternary runs**, the first 32 logged decisions were negative cell literals (variable IDs at most 300). At decision 32, the baseline held one 8,500-variable component and the comparison encoding held one 5,054-variable component, both with 0 partitioner calls, 0 component splits, 0 cache hits, and 0 SAT conflicts. Neither run reached decision 64 or 256 recursive calls before timing out. Counting clearly started, though the logs do not reveal the final decision count or where the rest of the time was spent.

## What the source does and does not explain

[`computeDecisionNode`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/modelCounters/ModelCounter.hh#L172) invokes the partitioner only when a component has more than 10 and fewer than 5,000 variables and no remaining priority variables. That explains why partitioning did not fire during the first 32 decisions, without proving whether partitioning later caused the stall.

The `-no-eqs` flag disables equivalence probing while leaving graph reduction and PaToH active (`core/Main.cc:216` -> `PartitionerInterface.cc:34` -> `ClauseBipartiteGraphPartitioner.cc:56`). Still, [`EquivManager::searchEquiv`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/utils/equiv.hh#L99) runs two-sided unit-propagation probing rather than full CDCL solves, so the stall could equally be a hard SAT subproblem after the first valid branch. Because the traces gave no strong signal, we did not run a third full trial with `-no-eqs`.

One read-only debugger attachment failed due to the host's ptrace restriction (saved in `exact_backend_full_baseline_stack.log`), and we did not alter kernel settings, leaving the exact stall point unresolved.

## Reproduction and artifacts

`exact_backend_benchmark.py` builds the four phased validation formulas from the parsimonious encoder and rephasing helpers, reads the existing full baseline and comparison CNFs untouched, and only starts the two full runs after all four validation counts pass:

```sh
python experiments/exact_backend_benchmark.py --full --seconds 120
```

The built binary sits at `exact_backend_tools/d4/d4`. To rebuild from the saved source and extracted Boost headers:

```sh
make -C experiments/exact_backend_tools/d4 -j2 COPTIMIZE='-O3 -DNDEBUG -I../boost/usr/include'
```

From a clean checkout, check out the commit above, apply `exact_backend_trace.patch`, download the Boost package URL listed in `exact_backend_provenance.json`, check its SHA256, and extract `data.tar.xz` into `exact_backend_tools/boost` (headers at `boost/usr/include`). Both upstream projects keep their own licenses.

`exact_backend_results.json` stores all six terminal records, commands, input and binary hashes, resource stats, parsed traces, and log paths. All runs have finished, giving independent exact validation while leaving the unrestricted ternary total open.
