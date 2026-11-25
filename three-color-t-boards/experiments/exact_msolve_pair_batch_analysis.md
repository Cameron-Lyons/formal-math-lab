# Pair-batch target one preserves pending work

In the preserved fourth build, `--max-pairs 1` reaches msolve as `-m1`.
`src/neogb/io.c:1262–1265` stores the positive value directly as `mnsel=1`.
It changes pair batching; it does not add a degree cutoff or an approximation
to the generating ideal. This is a read-only source assessment, with no new
solver run or source modification.

The active selector is `symbol.c:200`, `select_spairs_by_minimal_degree`.
It sorts the pending pair array and identifies its current minimal-degree
block. After choosing a count `nps`, it processes every selected pair in
the prefix `[0,nps)` at lines 296–380: for each LCM group, all pair endpoint
generators are collected, duplicate endpoints removed, and the appropriate
monomial multiples loaded into the matrix. Every selected S-pair is in the
row span of those multiples.

Only after constructing those rows, lines 392–393 execute:

```
memmove(ps, ps+nps, (psl->ld-nps)*sizeof(spair_t));
psl->ld -= nps;
```

The suffix of unselected pairs is therefore retained exactly. No pair is
discarded solely because it exceeds the batch target. Subsequent updates can
remove redundant pairs using the solver's existing criteria; those are
independent of the batching option. `update.c:325` finishes only when a
constant is found or the pending pair set is empty. The ordinary F4
initialization keeps `max_gb_degree=INT32_MAX` (`f4.c:394`), so target one
does not request a truncated basis.

## Actual tie behavior in this pinned version

Target one is **not a strict cap on selected pairs**, nor a guarantee that
all ties are grouped. The exact upstream code at `symbol.c:268–272` is:

```
if (npd > md->mnsel) {
    nps = md->mnsel;
    lcm = ps[nps].lcm;
    while (nps < npd && ps[nps+1].lcm == lcm) {
        nps++;
    }
}
```

Here `nps` is later used as a count. The extension starts from the first
unselected pair and looks one further ahead, rather than comparing against
the last selected pair. Thus it can select more than the target and can
split a tied-LCM run. For example, with pair LCMs `[A,B,B,C]` and target one,
it selects `[A,B]` and leaves `[B,C]`. With `[A,A,B]`, it selects only the
first `A`. No pair disappears in either case.

There is also a pre-existing boundary-read issue: when `nps=npd-1`, the
comparison reads `ps[npd]`, one beyond the current degree block. If that
block reaches the active-list end, this is beyond the active pair list
(possibly still within its allocated backing array). The loop's counter
still remains at most `npd`, and all matrix construction/removal is bounded
by that selected count. This inspection does not certify the boundary read
as safe, and no fix was made. The same upstream code applies to the previous
target sixteen; it is not introduced by target one.

The accurate operational description is therefore **pair-batch target one**.
It can reduce the working set compared with target sixteen, but symbolic
preprocessing can add many reducers even for a single selected pair. Matrix
rows, columns and memory are not bounded by the batch target. Only a
successfully completed and validated basis supports an exact quotient count;
a timeout or allocation failure remains incomplete.
