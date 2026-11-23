# Independent exact counting backend: d4

The official CRIL **d4** engine independently reproduced the four solved
validation counts, but neither unrestricted ternary trial completed. Both
full trials had 120-second wall limits and terminated with exit status 124.
Their recorded counts are `null`, not zero. No approximate mode, partial
count, or third full trial was used.

## Source and arithmetic

Repository: <https://github.com/crillab/d4>, pinned to its current official
head at inspection, `333370cc1e843dd0749c1efe88516e72b5239174`
(2023-05-17). The newer `crillab/d4v2` repository was also inspected; its
current interface is a library with a demo executable. The standalone d4
CLI was chosen for this independent backend experiment.

This is a different implementation from Ganak: a DPLL/knowledge-compilation
counter using its own component cache, a MiniSAT-derived SAT engine, and
PaToH partitioning. The original source was built locally with installed
GMP and zlib. Missing Boost 1.83 headers were extracted from a Debian
development package into `exact_backend_tools/boost`; nothing was installed
or changed in system directories.

The arithmetic is **arbitrary-precision integer**, not a rounded floating
result. Unweighted input literals receive weight 1 in
[`ParserProblem.cc`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/manager/ParserProblem.cc#L56).
[`core/Main.cc`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/core/Main.cc#L279)
detects integer weights and instantiates `ModelCounter<mpz_int>`. All six
logs explicitly confirm `Integer mode`. The `precision` option applies
only to the alternative floating-weight path and is irrelevant here.

Hashing does not introduce probabilistic count correctness: the cache
checks the serialized component header and then `memcmp`s its full data
before accepting a hit; see
[`CacheCNFManager.hh`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/manager/CacheCNFManager.hh#L172).
The SAT seed was fixed at 91648253, random branching has its default zero
frequency, and the upstream PaToH seed is 1.

All runs count **every CNF variable**. They do not pass a projection file;
d4 ignores the existing `c ind` comments. The encoders' functional
auxiliaries make ordinary model counting equal to board counting. Full
models retain orbit normalization, so any completed count would be
multiplied by 12 to recover all labeled ternary boards. No such full count
was obtained.

## Diagnostic change and options

`exact_backend_trace.patch` changes only logging: periodic statistics every
256 recursive calls, and a branch trace for the first 32 decisions and
subsequent powers of two. It does not alter search, simplification, cache
keys, or arithmetic. Source, binary, patch, bundled PaToH archive, Boost
package hashes, compiler, and linked libraries are recorded in
`exact_backend_provenance.json`.

Every run used the same counter options:

```text
-mc -ph=TRUE -rnd-seed=91648253
```

The defaults retain VSADS branch scoring, clause-bipartite partitioning,
graph reduction, equivalence probing, component splitting, and caching.
The `TRUE` phase name in this source produces negative branch literals
when reverse polarity is off, as confirmed by the traces. It therefore
follows the known all-false model of each rephased input initially.

## Completed validations and bounded full runs

| Input | Terminal result | CPU seconds | Wall seconds | Peak RSS, KB |
| --- | ---: | ---: | ---: | ---: |
| Binary, unrestricted | 168 | 0.213 | 0.269 | 49,752 |
| Binary, orbit normalized | 42 | 0.123 | 0.216 | 49,752 |
| Fully fixed valid ternary board | 1 | 0.036 | 0.050 | 62,168 |
| Published ternary prefix C | 2 | 9.392 | 11.171 | 51,632 |
| Full ternary baseline | timeout; no count | 96.546 | 120.041 | 611,220 |
| Full ternary comparison encoding | timeout; no count | 81.322 | 120.074 | 125,600 |

CPU and RSS in this table come from the wrapper's `os.wait4`, with CPU
equal to user plus system time. In this release,
[`cpuTime()`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/utils/System.hh#L74)
uses `gettimeofday`: the solver's reported time and the raw trace field
named `cpu` are actually **elapsed wall time**. Parsed JSON calls this
`solver_elapsed_seconds`. Its memory report reads `VmPeak`, a virtual
address-space size, rather than resident memory. The OS measurements above
avoid both ambiguities.

Prefix C completed after 55 recursive calls, 27 decisions and one
partitioner call, with no split components and no cache hits. This
independently verifies the count; the timing is not a controlled claim of
general superiority over Ganak.

The first 32 logged decisions in **each full trial** were cell variables
(absolute literal IDs at most 300), all negative. At the last recorded
decision the baseline had one 8,500-variable component and the comparison
encoding one 5,054-variable component. Both snapshots had zero completed
partitioner calls, zero split components, zero cache hits and zero SAT
conflicts. Neither run reached the next branch trace at decision 64 or
the periodic report at 256 recursive calls. Thus counting genuinely
started, but the logs do **not** establish the final decision count or
where the remaining time went.

## What the source does and does not explain

[`computeDecisionNode`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/modelCounters/ModelCounter.hh#L172)
calls the partitioner only when the component has more than 10 and fewer
than 5,000 variables and no remaining priority variables. That accounts
for the absence of partitioning in the recorded early full-instance
snapshots. It does not prove that a later partitioner call dominated the
timeout.

The exposed option `-no-eqs` would disable just equivalence probing while
leaving graph reduction and PaToH decomposition enabled. The option flows
from `core/Main.cc:216` through `PartitionerInterface.cc:34` to
`ClauseBipartiteGraphPartitioner.cc:56`. However,
[`EquivManager::searchEquiv`](https://github.com/crillab/d4/blob/333370cc1e843dd0749c1efe88516e72b5239174/utils/equiv.hh#L99)
does two-sided **unit-propagation** probing and conflict analysis, not
complete CDCL SAT solves. The observed pause could instead be a difficult
SAT subproblem after the first valid branch. No third full trial was
justified by these traces, so `-no-eqs` was not tested.

A read-only debugger attachment was attempted once to distinguish these
possibilities. The existing ptrace restriction rejected it; the failed
attempt is retained in `exact_backend_full_baseline_stack.log`. No kernel
settings were changed. The final bottleneck is therefore unresolved.

## Reproduction and artifacts

`exact_backend_benchmark.py` generates the four phased validation inputs
using the existing parsimonious encoder and verified model-rephasing
helpers. It reads the existing full baseline and comparison CNFs unchanged.
It launches the two full trials only after all four expected validation
counts have completed successfully.

```sh
python experiments/exact_backend_benchmark.py --full --seconds 120
```

The installed executable is `exact_backend_tools/d4/d4`. To rebuild from
the retained source and locally extracted headers:

```sh
make -C experiments/exact_backend_tools/d4 -j2 COPTIMIZE='-O3 -DNDEBUG -I../boost/usr/include'
```

For a fresh checkout, use the repository revision above and apply
`exact_backend_trace.patch` before building. Download the exact Boost
package URL and verify its SHA256 from `exact_backend_provenance.json`,
then extract its `data.tar.xz` member into `exact_backend_tools/boost`
(headers at `boost/usr/include`); a system package installation is not
needed. The upstream solver and extracted package retain their licenses.

`exact_backend_results.json` contains all six terminal records, exact
commands, input hashes, binary hash, resource usage, parsed traces, and log
paths. All runs have ended. This backend adds independent exact validation
and bounded search evidence; the unrestricted ternary count remains open.
