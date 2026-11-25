# Phase 9a: typed byte exponent vectors

Initial validation passes; independent review is pending. This is an API refactor
of frozen build eight, not a compressed representation. It changes no polynomial
identity, coefficient operation, field relation, pair-selection rule, or storage
width. No unrestricted T-board computation was run with this build.

The frozen executable is `msolve`, SHA-256
`317aeae6e3c82c81fe105b5ef4fc90f65880836f7ce17297f00d495015fd44be`.
The source-only patch against build eight is
[`typed-byte-vectors.patch`](typed-byte-vectors.patch), SHA-256
`82c8810eab2d175aaffb794593da4c0a30c1073eb8f7d3d5ba367f5076382e51`.
[`source.json`](source.json) pins all 102 C/header files, predecessor patches,
archive/commit, compiler, libraries, and build commands. Sixteen C/header files
change. The aggregate source-tree hash is
`8e6d9f043562e5a8f69b369fc021bae20e416aadac082eb7993be62c616a6730`.

## Allowed computation

The unchanged build-eight guards require an ordinary polynomial ring over F3,
degree reverse lexicographic order, deterministic exact linear algebra (`-l 2`),
one thread, reduced basis output (`-r 1 -g 1` or `-g 2`), and no genericity
transformation (`-c 0`). Input has 1–127 variables, an explicit `x_i^3-x_i`
generator for every variable, and all other input terms have coordinate exponents
at most two. Signature, trace, saturation, normal-form, elimination, rational
field and other-field modes remain rejected. The byte overflow guards remain
active. Ordinary polynomial exponents are never reduced modulo a storage width.

Unsupported paths were made type-correct where needed for compilation; this does
not enlarge the executable's allowed scope. Their runtime behavior is not claimed
as independently verified. In particular, the generic reset helper is tested for
layout compatibility, but ordinary `core_f4` does not call it.

## Representation and boundary invariants

[`stored_exp.h`](stored_exp.h) defines `stored_exp_t` as a distinct one-byte
structure, with a compile-time size assertion. Dense scratch remains `exp_t`
(`uint8_t`). A stored pointer cannot be used as a dense pointer or a scalar without
a compiler diagnostic. Production builds make incompatible-pointer and
integer-conversion warnings errors.

`ht_t.evl` is the logical lane count (degree plus variables in the allowed scope).
`ht_t.evbytes` is the physical vector stride. Both currently have the same value;
every allocation and stored-table stride uses `evbytes`, while arithmetic loops
use `evl`. The accessors check logical indices and representable values. Import,
export and copy check logical/physical agreement. Dense-to-stored import also
checks that lane zero equals the sum of the variable lanes and that the sum fits
in a byte. Private whole-slab copies check multiplication overflow but deliberately
do not interpret unused slots as valid monomials.

Stored reads return exactly the former byte. Hash weighting, equality, DRL
comparison, divisibility and short divisibility masks therefore receive the same
integers as before. `_Generic` boundary wrappers export stored operands to a
128-byte dense stack buffer when calling a dense-only routine. These wrappers
evaluate the operand once; `_Generic` selects its type without evaluating it.
Insertion order and hash IDs are unchanged.

The compiler-driven conversion covers direct accesses and cached aliases in
symbolic construction, LCMs, promotion, final interreduction, leading-monomial
extraction and complete basis output. The lexical audit reports 295 read, nine
write and 17 copy/import/export sites, with no raw stored scalar or memory-copy
bypass outside the API. This inventory complements semantic review; it is not
itself a proof of correctness.

## Storage ownership and growth

All three table constructors initialize/copy the physical stride. Legacy growth,
checked rounded growth, copy, reinitialization, staged promotion and generic
reset rebuild vector pointers using that stride. Dense import scratch and the
multiplied-row candidate live on the stack, so table reallocation cannot invalidate
them. Stored operands passed through the typed hash wrappers are exported before
the dense routine can grow a table.

The staged promotion ownership proof is unchanged: pack missing vectors in
increasing old symbolic ID, where destination is never greater than source;
restore an empty secondary table; insert in increasing column order. The same
private arrays are freed and the shared random weights/divisibility data remain
borrowed. Compaction now calls the checked overlap-safe stored-copy API.

The coefficient linear-algebra sources and raw-input/model guard headers are
byte-identical to build eight. This refactor does not repair unrelated upstream
unchecked allocation sites. A crash, allocation error, overflow, or missing export
marker remains an incomplete computation, never a zero count.

## Validation

- [`validation.json`](validation.json): 26 paired completed g1/g2 comparisons
  against frozen eight. All exports and all symbolic reservation, staging,
  promotion reservation/capacity and imported-column event sequences match.
  Fixtures include 11 exhaustively counted small ideals, the known six-completion
  fiber, and 127 independent field domains (dimension `3^127`). Both Python
  monomial counters agree. There are 56 promotion, four staging and 72 symbolic
  reservation events in each side's logs.
- [`table_check.json`](table_check.json): actual `data.h`, `hash.c` and `order.c`
  under ASan and UBSan; 2,032 vector round trips, all 256 scalar byte values,
  2,100 independent DRL/divisibility/LCM comparisons, deliberate hash collisions,
  13 staging cases, and an exact 150,000-entry non-power-capacity row/table
  comparison. Subsequent copy, clean, reinitialize, legacy growth and generic
  reset/reinsert pass. Seventeen invalid API calls and ten allocation-failure
  injections exit nonzero without sanitizer findings. The only stubbed solver
  helpers are clocks.
- [`guard_check.json`](guard_check.json): all 39 inherited malformed-input and
  unsupported-mode cases reject before a completion marker or basis export.
- [`compile_api_check.json`](compile_api_check.json): ten dense/stored pointer and
  scalar misuse cases fail compilation; the valid typed example compiles.
- [`source_audit.json`](source_audit.json): access/copy inventory, unchanged
  coefficient kernels and guard headers, and physical-stride audit.

These small checks establish regression
evidence, not a speedup, a memory saving, or an unrestricted exact T-board count.

## Reproduction and preserved attempts

`prepare.py` starts from the pinned v0.11.0 archive and applies the preserved
predecessor patches. `refactor.py`, `accessor_conversion.py`, and `boundaries.py`
then reproduce this source from immutable build-eight bytes; `build.py` performs
autogen/configure/make with one build job. `compile.py` records each incremental
build attempt. The mechanical conversion is intentionally separate from the
explicit boundary edits and validation.

For an existing prepared tree, the source transformation sequence is:

```sh
python experiments/exact_msolve_vector_api_tools/refactor.py
python experiments/exact_msolve_vector_api_tools/accessor_conversion.py
python experiments/exact_msolve_vector_api_tools/boundaries.py
python experiments/exact_msolve_vector_api_tools/compile.py
```

The validation checks are `table_check.py`, `guard_check.py`, `compile_api_check.py`,
`source_audit.py`, and `PYTHONPATH=experiments python .../validate.py`.
The basis runner refuses to overwrite prior test input/basis files. Copy or move
the terminal test set to a new archival directory before an intentional rerun.

`candidate1/` preserves executable `86d7819c…` and its passing initial evidence.
`candidate2/` preserves executable `63b1ee04…`, its complete source patch and
passing tests. The final revision only closes three excluded-mode zeroing
boundaries that had different upstream cast spelling. The same test suite was
rerun on the final bytes. Initial compiler failures and the preparation check
failure are retained; none produced an accepted solver result.

No nibble packing is implemented or authorized by this report. A later packed
representation still needs separate source, overflow, alias, stride and basis
review. A temporary exponent above 15 must not be silently truncated or declared
impossible from the present field-domain proof.
