# Complete two-row symmetry split

`exact_symmetry_split.py` enumerates every coloring of the first two rows using
Cartesian coordinates `(row, x)` for horizontal reflection. Each four-character
prefix lists the top T in order: top, left, middle, right. Global color
permutations and horizontal reflection preserve board validity and biject the
completion sets of caps in the same orbit.

Pick one canonical cap `r` per orbit and let `c_r` be its number of **raw
labeled completions** with no extra symmetry constraints. The unrestricted
board count is

```text
N = sum_r |orbit(r)| * c_r.
```

The symmetry action on caps is not free: there are ten ternary orbits whose
sizes add up to 81, so multiplying every cap count by 12 would be wrong. This
formula does not assume that the full-board action is free.

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

The witness column only shows coverage among saved boards, **not completion
counts**. All 1,557 distinct saved boards were checked for all 81 patterns. All
5 published witnesses and all 1,430 extended witnesses belong to cap `0000`,
while the 161-board gauge certificate adds the other four covered caps (with
duplicates across sources removed). Having zero saved witnesses for the other
five caps does not mean those caps have no completions. Source hashes and
per-source counts are in `exact_symmetry_split_coverage.json`.

The manifest stores every orbit member, stabilizer order, and digest.
Validation rebuilds the entire partition and rejects any edit to orbit
membership, weights, representatives, or coverage, instead of just checking
that the weights sum to 81.

## Completed-count audit

The CLI `aggregate` subcommand reads prime-Fourier backend JSON results
(default model `prime-all:29`) and requires exactly one result per canonical
four-cell prefix. Before accepting any branch count, it verifies:

- Literal `COMPLETE` status, completed standard basis, normal exit, and no
  timeout or error messages. Partial statuses and `COMPLETE_FROM_LEADING_IDEAL`
  are rejected here.
- Exact prefix and model identity, raw prefix-fiber scope, ordinary polynomial
  ring, field and color map, exact free cells, and no symmetry normalization or
  multiplier.
- Independent regeneration of the model from geometry and prefix, checking both
  the model-data hash and every byte of the saved Singular input without
  importing the backend adapter.
- Matching log completion markers, standard-basis attestation, exact bigint
  Hilbert count, full leading-monomial export, and provenance.
- Agreement across both saved Python monomial counts, the Hilbert count, and
  the decimal count, followed by an independent recount of the leading ideal
  via `exact_standard_monomials.py` in Python arbitrary-precision integers.

This audits saved backend artifacts rather than giving an independent proof of
Singular's Gröbner basis; recounting runs only after the basis-completion and
full-export checks pass. The script never invokes Singular or runs any ternary
search.

Only when all ten branches pass does the script write `status=COMPLETE` and
`full_count_decimal`. Otherwise it exits with status 2, `status=REFUSED`,
`exact_total_available=false`, and no numerical total. Duplicate JSON keys and
duplicate case records are rejected. In Python, `aggregate` accepts only
`VerifiedCount` objects created by the artifact auditor or the exhaustive
binary check, never raw dictionaries.

## Independent binary validation

The test suite exhausts all assignments to the 25 binary cells, pruning only
when a completed T repeats an earlier pattern. It visits 119,665 partial
assignments and finds all 168 valid binary boards (each verified by a separate
pattern-set check), confirms closure under all symmetries, and counts all 16
cap fibers directly:

| Binary cap representative | Orbit size | Raw completions | Weighted contribution |
| --- | ---: | ---: | ---: |
| 0000 | 2 | 24 | 48 |
| 0001 | 4 | 9 | 36 |
| 0010 | 2 | 14 | 28 |
| 0011 | 4 | 3 | 12 |
| 0101 | 2 | 2 | 4 |
| 0111 | 2 | 20 | 40 |
| Total | 16 | 72 | **168** |

All 97 caps across the binary and ternary palettes are also checked against a
separate positional reflection implementation. The test suite includes 59
rejection tests (missing, duplicate, partial, errored, mismatched, and
corrupted inputs), exact zero and large-integer aggregation tests, and an audit
of the existing completed six-completion nine-row artifact (which is rightly
rejected by cap aggregation because its prefix length is wrong). No ternary
completion search runs during these checks.

## Reproduction

```sh
python experiments/exact_symmetry_split_check.py
python experiments/exact_symmetry_split.py manifest --colors 3 --output experiments/exact_symmetry_split_manifest_3.json
python experiments/exact_symmetry_split.py coverage --output experiments/exact_symmetry_split_coverage.json
```

Once all ten cap runs finish, aggregate them with:

```sh
python experiments/exact_symmetry_split.py aggregate --manifest experiments/exact_symmetry_split_manifest_3.json --model prime-all:29 --output experiments/exact_symmetry_split_total.json RESULT_0000.json RESULT_0001.json RESULT_0010.json RESULT_0011.json RESULT_0012.json RESULT_0101.json RESULT_0102.json RESULT_0111.json RESULT_0112.json RESULT_0121.json
```

No ternary cap solver run was started here, and no completed ternary cap count
exists yet. The unrestricted total remains uncomputed; this manifest makes any
future complete split auditable.
