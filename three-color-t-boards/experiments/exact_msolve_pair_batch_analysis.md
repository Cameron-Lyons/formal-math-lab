# Pair-batch target one preserves pending work

In the fourth build, `--max-pairs 1` passes `-m1` to msolve. `src/neogb/io.c:1262-1265` stores this directly as `mnsel = 1`. It only controls pair batching and introduces no degree cutoff or approximation to the ideal. This note is a read-only source audit with no solver run or code change.

The active selector is `select_spairs_by_minimal_degree` (`symbol.c:200`). It sorts pending pairs, identifies the current minimal-degree block, picks a count `nps`, and processes `[0, nps)` in lines 296-380: for each LCM group, it gathers endpoint generators, drops duplicates, and loads the required monomial multiples into the matrix. Every selected S-pair lies in the row span of those rows.

Only after building those rows do lines 392-393 remove the processed prefix:

```
memmove(ps, ps+nps, (psl->ld-nps)*sizeof(spair_t));
psl->ld -= nps;
```

All unselected pairs remain in the list. No pair is dropped simply for exceeding the batch target. Later updates still prune redundant pairs via the solver's standard criteria, independently of `-m`. `update.c:325` terminates only when a constant appears or the pair list is empty, and ordinary F4 initializes `max_gb_degree = INT32_MAX` (`f4.c:394`), so target 1 computes a full, untruncated basis.

## Actual tie behavior in this pinned version

Target 1 is **neither a strict cap on selected pairs nor a guarantee that tied LCMs stay together**. The upstream code at `symbol.c:268-272` is:

```
if (npd > md->mnsel) {
    nps = md->mnsel;
    lcm = ps[nps].lcm;
    while (nps < npd && ps[nps+1].lcm == lcm) {
        nps++;
    }
}
```

Because `nps` is used as a count, `ps[nps]` is actually the first *unselected* pair, and the loop compares it against `ps[nps+1]` rather than against the last selected pair. As a result, it can exceed the target or split a run of equal LCMs:

- For pair LCMs `[A, B, B, C]` with target 1, it selects `[A, B]` and leaves `[B, C]`.
- For `[A, A, B]` with target 1, it selects only the first `A`.

No pair is lost in either case.

There is also a pre-existing boundary read: when `nps == npd - 1`, `ps[nps+1]` reads `ps[npd]`, one slot past the current degree block (and past the active pair list if the block reaches its end, though possibly still inside the backing allocation). The counter `nps` stays at most `npd`, bounding all matrix construction and removal. We did not certify that read as safe or patch it; the exact same upstream code runs under target 16 as under target 1.

The accurate label for `-m1` is **pair-batch target one**. It can cut working memory relative to target 16, though symbolic preprocessing can still pull in many reducers from a single pair, so memory is not bounded by the batch target. Only a completed, validated basis gives an exact count; timeouts and allocation failures leave the count unknown.
