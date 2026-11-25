# Independent rounded promotion-capacity review

Reviewed patch:
`exact_msolve_rounded_promotion_tools/rounded-promotion-capacity.patch`, SHA256
`d569538b42f58dbf7160621891918cddc9496347a8229f350350eb5977539461`.
Reviewed executable SHA256:
`cebd842aa617f09725a1f5429ebc822da238563f142b14993cccb85312d1874c`.
Only the guarded promotion reserve operation changes relative to the third
build; the upstream grower remains unchanged.

## Arithmetic and memory review

The new reserve helper computes `eld + missing + 1`, retaining a spare entry,
and rounds up to a multiple of 65,536 exponent slots. Bucket capacity remains
a power of two at least twice the exponent capacity. It rejects unsupported
layouts, capacities above `2^30` entries or `2^31` buckets, and arithmetic
that would exceed the platform allocation-size limit. The bucket limit avoids
an existing legacy reinsertion path that narrows bucket count to 32 bits.
The spare entry avoids exact-fill boundary assumptions in later insertion
code.

For the measured failing reservation:

```text
load                      2,080,795
missing                      55,218
required including spare  2,136,014
rounded exponent capacity 2,162,688
bucket capacity           8,388,608
```

The previous doubling would have requested 4,194,304 exponent slots. The new
size is sufficient without requiring exponent capacity itself to be a power
of two. Source inspection found that exponent capacity is used for linear
array bounds/allocation, while only bucket indexing uses a power-of-two mask.

Each of the four possible reallocations uses a checked temporary pointer.
Failure terminates nonzero before any completed export. The old contiguous
exponent block is saved before reallocating the pointer array; after the data
block moves, **every** pointer, including slot zero, is rebuilt from the new
block. Existing metadata and exponent-array positions are retained. If
buckets grow, the map is cleared and all existing entry IDs are rehashed
using the same probing sequence; IDs and insertion order do not change.
The final capacities are committed only after the complete operation.

The reserve helper does not move random hash multipliers, divisor-mask data,
or other arrays shared with secondary tables. Copy/clean/reset operations use
the stored capacities directly. Legacy doubling preserves the power-of-two
bucket count and the bucket-to-entry capacity ratio even after exponent
capacity becomes a non-power-of-two multiple of 65,536. Existing upper-limit
and allocation-failure behavior in untouched legacy routines is not repaired
by this patch.

## Independent executable checks

`exact_msolve_rounded_capacity_check.py` extracts the exact reserve helper and
tests it under address and undefined-behavior sanitizers. It passed:

- Three real reallocation/collision cases, including a non-power-of-two
  exponent capacity of 196,608 and the branch where buckets need not grow.
  These check all reconstructed pointers, retained metadata/exponents, and
  retrieval of existing IDs after collision-heavy rehashing.
- Failure injection at each of the four reallocations, with a clean nonzero
  exit and no successful completion.
- Seven independent capacity plans, including the measured requirement,
  no-growth cases, exact-boundary rounding, and the supported upper bound.
  Large plans fail deliberately at the first allocation instead of allocating
  their requested storage.
- Thirteen invalid-layout/limit/overflow cases. Three use a native harness
  with `SIZE_MAX` restricted to model 32-bit allocation guards; this is not
  claimed as a separately compiled 32-bit executable.

Results are retained in `exact_msolve_rounded_capacity_results.json`.

All 25 small completed-basis comparisons passed with tiny initial hash size
`-s4`, including five cases in characteristic two. The candidate and previous
builds exported byte-identical full reduced bases, and both agree with an
independent exact Python Buchberger implementation. Logs contain **ten actual
rounded-growth events**, so these tests exercise the new reserve operation.
Results and hashes are in `exact_msolve_rounded_review_results.json`; raw
fixtures are under `exact_msolve_rounded_review_runs/`.

The patch owner's separate actual-upstream compatibility harness also passed
and its assertions were reviewed here. Starting from non-power-of-two
capacity 196,608, it exercises real legacy growth to 393,216, copying,
cleaning, reinitialization, secondary-table initialization/growth, and
basis/pair reset/reinsertion, in both ordinary and forced-collision modes.
It also verifies the exact-boundary spare entry. Existing IDs remain stable
except during reset, whose intentional renumbering is checked by comparing
the referenced exponent vectors. Only the short divisibility-mask calculation
and timing functions are stubbed. These results are attributed to the owner's
`exact_msolve_rounded_promotion_tools/compatibility_check.json` and harness,
not presented as a duplicate independent run. Patch and executable hashes
were reconfirmed unchanged after that result.

**Review complete: no correctness issue found for the guarded path.** The
independent arithmetic/allocation/basis checks and the separately attributed
actual caller-compatibility tests support a bounded full-input trial.

```sh
python experiments/exact_msolve_rounded_capacity_check.py
python experiments/exact_msolve_sparse_review.py --baseline experiments/exact_msolve_missing_promotion_tools/msolve --candidate experiments/exact_msolve_rounded_promotion_tools/msolve --artifact-prefix exact_msolve_rounded_review --initial-hash-log2 4
```

No full T-board computation was run by this reviewer. A memory failure,
timeout, incomplete export, or incomplete basis remains an incomplete result,
never an exact count of zero.
