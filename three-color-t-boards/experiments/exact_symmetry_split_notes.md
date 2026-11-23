# Complete two-row symmetry split

`exact_symmetry_split.py` independently enumerates every coloring of the first
two rows, using Cartesian coordinates `(row,x)` for horizontal reflection.
The four-character prefix is the ordered top T: top, left, middle, right.
Global palette permutations and reflection preserve validity and give
bijections between completion sets of caps in the same orbit.

For one canonical cap `r` from each orbit, let `c_r` be the number of **raw
labeled completions of that exact fixed prefix**, with no further symmetry
restriction. The unrestricted total is

```text
N = sum_r |orbit(r)| * c_r.
```

The cap action is not free. There are ten ternary orbits, whose sizes sum to
81; multiplying every cap count by 12 would be wrong. This partition formula
does not require the full-board action to be free.

| Representative | Prefix rows | Cap orbit size | Cap stabilizer size | Saved witness boards |
| --- | --- | ---: | ---: | ---: |
| 0000 | 0 / 000 | 3 | 4 | 1,519 |
| 0001 | 0 / 001 | 12 | 1 | 26 |
| 0010 | 0 / 010 | 6 | 2 | 0 |
| 0011 | 0 / 011 | 12 | 1 | 4 |
| 0012 | 0 / 012 | 12 | 1 | 0 |
| 0101 | 0 / 101 | 6 | 2 | 0 |
| 0102 | 0 / 102 | 6 | 2 | 0 |
| 0111 | 0 / 111 | 6 | 2 | 2 |
| 0112 | 0 / 112 | 12 | 1 | 6 |
| 0121 | 0 / 121 | 6 | 2 | 0 |

The witness column is coverage evidence, **not a completion count**. The
1,557 distinct saved boards were independently checked for all 81 patterns.
All five published witnesses and all 1,430 extended witnesses have cap type
0000. The 161-board gauge certificate supplies the other four covered types,
with overlap across sources removed. The absence of witnesses for the five
remaining cap types does not establish impossibility. Source hashes and
per-source coverage are saved in `exact_symmetry_split_coverage.json`.

The manifest includes every actual orbit member and stabilizer order, plus a
digest. Validation regenerates the complete partition and rejects any change
to membership, weights, representatives, or coverage. It does not merely
check that the supplied weights happen to sum to 81.

## Completed-count audit

The command-line aggregate accepts the existing prime-Fourier backend JSON
results, default model `prime-all:29`. It requires exactly one result for each
of the ten canonical four-cell prefixes. The following are checked before a
count can contribute:

- Literal `COMPLETE` status, completed standard basis, normal termination,
  and no timeout/error diagnostics. Partial statuses and
  `COMPLETE_FROM_LEADING_IDEAL` are deliberately refused by this interface.
- Exact prefix/model identity, raw prefix-fiber scope, ordinary polynomial
  ring, coefficient field and color map, correct free cells, and no symmetry
  normalization or multiplier.
- The model is regenerated from geometry and the prefix. Its model-data hash
  and every byte of the actual retained Singular input must match the expected
  definition and exact-count procedure. The backend adapter is not imported.
- Actual log completion markers, standard-basis attestation, exact bigint
  Hilbert result, complete leading-monomial export, and provenance agree.
- Both saved Python monomial counts, the Hilbert count, and the decimal count
  agree. The completed leading ideal is then independently recounted using
  `exact_standard_monomials.py` and Python arbitrary-precision integers.

This is an audit of the retained completed backend artifacts, not an
independent proof of its Gröbner basis. Recounting is permitted only after its
standard-basis and complete-export attestations pass. The script never runs
Singular or starts a ternary search.

Only after all required results pass does the output have `status=COMPLETE`
and `full_count_decimal`. Failure instead returns exit status 2 with
`status=REFUSED` and `exact_total_available=false`, with no numerical total.
Duplicate JSON keys are rejected, as are duplicate case records. The
Python `aggregate` API consumes only `VerifiedCount` objects produced by a
completed-artifact audit or the exhaustive binary check; arbitrary count
dictionaries are not accepted.

## Independent binary validation

The test enumerates all assignments to the 25 binary cells, pruning only
when a fully assigned T repeats an earlier pattern. It visits 119,665 partial
assignments and finds all 168 valid boards. A separate direct pattern-set
check verifies every result. Every symmetry image is in that exhaustive set,
and all 16 cap fibers are explicitly counted.

| Binary cap representative | Orbit size | Raw completions | Weighted contribution |
| --- | ---: | ---: | ---: |
| 0000 | 2 | 24 | 48 |
| 0001 | 4 | 9 | 36 |
| 0010 | 2 | 14 | 28 |
| 0011 | 4 | 3 | 12 |
| 0101 | 2 | 2 | 4 |
| 0111 | 2 | 20 | 40 |
| Total | 16 | 72 | **168** |

All 97 caps across the binary and ternary palettes are additionally checked
against a separate direct positional reflection action. The checks include
59 rejection cases for missing, duplicate, partial, erroneous, mismatched,
and corrupted inputs; exact zero and large-integer aggregation; and an audit
of the existing completed six-completion nine-row artifact. That artifact
correctly fails the subsequent cap aggregation because its prefix has the
wrong length. No ternary completion search occurs in these checks.

## Reproduction

```sh
python experiments/exact_symmetry_split_check.py
python experiments/exact_symmetry_split.py manifest --colors 3 --output experiments/exact_symmetry_split_manifest_3.json
python experiments/exact_symmetry_split.py coverage --output experiments/exact_symmetry_split_coverage.json
```

When all ten cap computations have completed, pass their result paths to:

```sh
python experiments/exact_symmetry_split.py aggregate --manifest experiments/exact_symmetry_split_manifest_3.json --model prime-all:29 --output experiments/exact_symmetry_split_total.json RESULT_0000.json RESULT_0001.json RESULT_0010.json RESULT_0011.json RESULT_0012.json RESULT_0101.json RESULT_0102.json RESULT_0111.json RESULT_0112.json RESULT_0121.json
```

No cap computation has been launched by this work, and no complete ternary
cap result is currently available. The unrestricted exact total remains
uncomputed; this manifest makes a future complete case split auditable.
