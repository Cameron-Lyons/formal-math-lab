# Sixth build, F3-enabled variant (6b)

This separate build changes exactly one guard in staged symbolic promotion, widening `st->fc == 2` to `(st->fc == 2 || st->fc == 3)`. The frozen F2-only sixth build stays unchanged. All other mode guards remain: exact option 2, single thread, no trace, no normal form, no final reduction, no elimination block, ordinary basis export, and actual basis-capacity growth. Characteristics other than 2 and 3 keep the older path.

The bitset matrix kernel remains F2-only. F3 runs still use the generic exact coefficient arithmetic and gain only the coefficient-independent post-LA exponent compaction. The compaction helper, hash lookup, reservation, import order, and ownership logic are byte-identical to build 6.

- Pinned upstream: msolve `v0.11.0`, commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`, archive SHA-256 `0f53c278ce2c3d46600348e945313e467314d296d275f2978f92c6b6b8e2224a`
- Six predecessor patches, build commands, environment, and local libraries: recorded in `source.json`
- One-line incremental patch: `enable-f3-staging.patch`, SHA-256 `96396c6b6a15e2ae1be84fdc968c21c62a87065acb5c4e2b7897b5e14cc75850`
- Frozen executable `msolve` SHA-256: `9e17f4224f282a2effa0d7b39a2be793db9f186499313ca395163dee53b4bc3a`
- Modified `convert.c` SHA-256: `1d5671e2df9cee6b96c8f325073e2d633e1f3a0057fa45c66f9e254550d2c92a`
- Unchanged `hash.c` SHA-256: `8ff90c83d8decbec184c023cc71301a40273f9dfb2d6566e924b488b121c2f98`

See `../exact_msolve_staged_promotion_tools/README.md` for the overlap-direction proof, insertion-order invariant, private/borrowed ownership audit, and memory-model limits. Because the compaction code is identical, the 49 upstream hash/reuse cases and 1,200 independent helper checks (covering allocation failures, zero-missing stages, inverse-map permutations, and later legacy reuse) carry over directly.

## Validation

- `validate.py` and `validation.json`: 20 completed `-g 1` / `-g 2` comparisons against the frozen F2-only sixth build. Eight F3 ideals include the audited natural 19-variable, 99-generator nine-row fiber, whose quotient dimension is 6 directly (divisor 1) across both bigint counters. Two F3 runs trigger staged hash import with nonzero F3 coefficients, and no F3 run emits an F2 bitset diagnostic. F2 and F5 mixed-ideal regressions match byte-for-byte (F2 stages; F5 does not). Note that several F3 fixtures deliberately use nonradical `x^3 - 1` domains whose quotient dimensions include multiplicity rather than counting F3 points; the board fixture uses its audited radical model.
- Independent review (`../exact_msolve_staged_f3_review_results.json`): full C-tree diff confirms only the caller guard changed across all 61 C files (60 files identical, including `hash.c`). Twelve F3 ideals produce 24 completed full bases matching both build 6 and Python Buchberger (9 also match exhaustive F3 enumeration), exercising 3 F3 staging rounds and 0 F2 bitset rounds.

No full T-board solve was run during validation.
