# Sixth build, F3-enabled variant (6b)

This separately preserved variant changes exactly one source guard from
`st->fc == 2` to `(st->fc == 2 || st->fc == 3)` for staged symbolic promotion.
The frozen F2-only sixth build remains unchanged. Every other mode restriction
is retained: exact option two, serial execution, no trace/normal form/final
reduction/elimination block, ordinary basis export, and actual basis-capacity
growth. Fields other than two and three retain the old path.

The characteristic-two bitset kernel remains **F2-only**. F3 uses the existing
generic exact coefficient arithmetic; only its coefficient-independent
post-LA exponent-storage compaction is newly enabled. The compaction helper,
hash lookup, reservation, import ordering and ownership logic are byte-for-byte
identical to the reviewed sixth build.

Pinned upstream remains v0.11.0, commit
`cc044551f8e202d00691990fd3fd0b1226a88ea2`; archive SHA256
`0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`.
`source.json` records all six predecessor patches, exact build commands,
environment and local libraries. Apply the one-line incremental
`enable-f3-staging.patch`, SHA256
`96396c6b6a15e2ae1be84fdc968c21c62a87065acb5c4e2b7897b5e14cc75850`.

Frozen executable `msolve` has SHA256
`9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`.
Modified `convert.c` has SHA256
`1d5671e2df9cee6b96c8f325073e2d633e1f3a0057fa45c66f9e254550d2c92a`.
Unchanged `hash.c` has SHA256
`8ff90c83d8decbec184c023cc71301a40273f9dfb2d6566e924b488b121c2f98`.

The overlap-direction proof, stable insertion order, private/borrowed ownership
audit and exact memory-model limitations are in
`../exact_msolve_staged_promotion_tools/README.md`. The 49 actual upstream
owner hash/reuse cases and 1,200 independently checked helper cases apply to
the identical compaction code here. They include allocation failures,
zero-missing stages, inverse-map permutations and subsequent legacy reuse.

`validation.py` / `validation.json` record twenty completed g1/g2 comparisons
against the frozen F2-only sixth build. Eight F3 ideals include the parent-
audited natural 19-variable/99-generator fixed nine-row fiber. Its quotient
dimension is six by both independent bigint counters, directly with divisor
one. Two F3 runs exercise actual staged hash import with nonzero coefficients
in characteristic three. No F2 bitset diagnostic occurs in any F3 run.

F2 and F5 mixed-ideal regressions also match byte-for-byte; F2 still stages
and F5 does not. Some F3 fixtures use nonradical `x^3-1` domains deliberately:
their expected quotient dimensions count multiplicity and must not be read
as F3-rational point counts. The natural board fixture uses its separately
audited radical finite-field model.

Independent review passed in
`../exact_msolve_staged_f3_review_results.json`. An exact C-tree comparison
confirms the sole caller-guard change and 60 other identical C files,
including `hash.c`. Twelve F3 fixtures produce 24 completed full bases that
match both the frozen sixth build and a Python Buchberger reference. Nine
also match exhaustive F3 enumeration. Three actual F3 staging rounds and
zero F2 bitset rounds are recorded.

All owner/reviewer validation runs are terminal. No full T-board solver was
launched by either build-validation task.
