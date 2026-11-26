# Phase 9a: typed byte exponent vectors

Initial validation passes; independent review is still pending. This build is an API refactor of frozen build 8, not a compressed storage format. It leaves polynomial identities, coefficient arithmetic, field relations, pair selection, and 1-byte exponent storage width unchanged. No unrestricted T-board solve was run with this build.

- Frozen executable `msolve` SHA-256: `317aeae6e3c82c81fe105b5ef4fc90f65880836f7ce17297f00d495015fd44be`
- Source-only patch against build 8: [`typed-byte-vectors.patch`](typed-byte-vectors.patch), SHA-256 `82c8810eab2d175aaffb794593da4c0a30c1073eb8f7d3d5ba367f5076382e51`
- Manifest: [`source.json`](source.json) pins all 102 C/header files (16 changed), predecessor patches, archive/commit, compiler, libraries, and build commands; aggregate source-tree hash `8e6d9f043562e5a8f69b369fc021bae20e416aadac082eb7993be62c616a6730`

## Allowed computation

All build-8 scope guards stay active: ordinary F3 polynomial ring, DRL order, exact sparse linear algebra (`-l 2`), one thread, reduced basis export (`-r 1 -g 1` or `-g 2`), and no genericity transform (`-c 0`). Inputs must have 1 to 127 variables, an explicit `x_i^3 - x_i` generator for every variable, and coordinates at most 2 in all other initial terms. Signature, trace, saturation, normal-form, elimination, rational, and other-field modes remain rejected, byte overflow checks stay on, and exponents are never reduced modulo storage width.

Unsupported code paths were updated only enough to stay type-correct during compilation, which does not widen the allowed runtime scope or mean those paths were verified. Generic `reset_hash_table` is tested for layout compatibility, though ordinary `core_f4` never calls it.

## Representation and boundary invariants

[`stored_exp.h`](stored_exp.h) wraps stored exponents in a distinct 1-byte struct `stored_exp_t` with a compile-time size assertion, while dense scratch stays `exp_t` (`uint8_t`). Using a stored pointer as a dense pointer or scalar triggers a compiler error under the production flags (which treat incompatible-pointer and integer-conversion warnings as errors).

`ht_t.evl` tracks logical lanes (degree plus variables in the allowed scope) and `ht_t.evbytes` tracks physical byte stride. Both hold the same value today, but every allocation and table stride uses `evbytes` while arithmetic loops use `evl`. Accessors check logical indices and representable values; import, export, and copy verify logical/physical agreement. Dense-to-stored import also verifies that lane 0 equals the sum of variable lanes and fits in a byte. Whole-slab copies check multiplication overflow without interpreting unused slots as monomials.

Reads return the exact same byte as build 8, so hashing, equality, DRL comparison, divisibility, and short divisibility masks get identical inputs. `_Generic` boundary wrappers copy stored operands into a 128-byte dense stack buffer before calling dense-only routines, evaluating each operand once (`_Generic` inspects the type without evaluating the expression). Insertion order and hash IDs stay identical.

Compiler-driven conversion covers direct reads and cached aliases across symbolic construction, LCMs, promotion, final interreduction, leading-monomial extraction, and basis export. The lexical audit counts 295 read, 9 write, and 17 copy/import/export sites, with zero raw scalar or memory-copy bypasses outside the API (supporting, rather than replacing, semantic review).

## Storage ownership and growth

All three table constructors initialize or copy `evbytes`. Legacy growth, checked rounded growth, copy, reinitialization, staged promotion, and generic reset rebuild pointers using `evbytes`. Because dense import scratch and multiplied-row candidates live on the stack, table growth cannot invalidate them, and typed wrappers export stored operands before any dense helper can grow a table.

Staged promotion keeps its exact ownership proof (pack missing vectors in increasing old symbolic ID so destination <= source, restore an empty secondary table, insert in increasing column order, keep shared weights/divisibility data borrowed), now using the checked overlap-safe stored-copy API.

Coefficient linear-algebra files and raw-input/model guard headers are byte-identical to build 8. Unrelated upstream unchecked allocations are not fixed here; any crash, allocation error, overflow, or missing completion marker leaves the count unknown and never implies zero.

## Validation

- [`validation.json`](validation.json): 26 paired completed `-g 1` / `-g 2` runs vs. build 8. Every export and every symbolic reservation, staging, promotion reservation/capacity, and imported-column log sequence matches identically (11 exhaustively counted small ideals, the six-completion fiber, and 127 independent domains giving `3^127`, verified by both Python counters; 56 promotions, 4 stagings, and 72 symbolic reservations per side).
- [`table_check.json`](table_check.json): actual `data.h`, `hash.c`, and `order.c` under ASan and UBSan (stubbing only clocks): 2,032 vector round trips, all 256 byte values, 2,100 independent DRL/divisibility/LCM checks, forced hash collisions, 13 staging cases, a 150,000-entry non-power-capacity row/table test, subsequent copy/clean/reinit/legacy growth/reset, 17 invalid API calls, and 10 allocation-failure injections exiting nonzero cleanly.
- [`guard_check.json`](guard_check.json): all 39 malformed-input and unsupported-mode rejections pass cleanly before any completion marker or basis output.
- [`compile_api_check.json`](compile_api_check.json): 10 dense/stored pointer and scalar misuse snippets fail to compile, while the valid typed snippet compiles.
- [`source_audit.json`](source_audit.json): access/copy counts, unchanged coefficient kernels and guard headers, and physical-stride audit.

These tests confirm regression equivalence and do not claim a speedup, memory reduction, or unrestricted T-board count.

## Reproduction and preserved attempts

`prepare.py` unpacks pinned `v0.11.0` and applies predecessor patches; `refactor.py`, `accessor_conversion.py`, and `boundaries.py` reproduce the source from immutable build-8 bytes; `build.py` runs autogen, configure, and single-job `make`; `compile.py` logs incremental build attempts.

On an already prepared tree:

```sh
python experiments/exact_msolve_vector_api_tools/refactor.py
python experiments/exact_msolve_vector_api_tools/accessor_conversion.py
python experiments/exact_msolve_vector_api_tools/boundaries.py
python experiments/exact_msolve_vector_api_tools/compile.py
```

Run `table_check.py`, `guard_check.py`, `compile_api_check.py`, `source_audit.py`, and `PYTHONPATH=experiments python .../validate.py` to repeat validation. Because the basis runner never overwrites existing test files, copy or move prior outputs to an archive directory before rerunning.

`candidate1/` saves executable `86d7819c...` and its passing initial tests; `candidate2/` saves `63b1ee04...`, its patch, and passing tests. The final revision only closed three excluded-mode zeroing sites that used a different upstream cast spelling, and reran the full suite. Early compiler errors and the preparation check failure are kept on disk; none produced an accepted solver result.

No nibble packing is implemented or authorized here. A future packed build will need separate source, overflow, alias, stride, and basis review, and any temporary exponent above 15 must fail cleanly rather than being truncated or assumed impossible.
