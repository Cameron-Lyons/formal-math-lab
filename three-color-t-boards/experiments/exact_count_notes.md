# Exact model-counting experiment

The unrestricted ternary count was **not obtained**. This experiment builds a count-preserving Boolean model and verifies it on smaller exact cases; it gives an exact formulation without claiming the full run will finish in practical time.

## Encoding and proof of count preservation

For `q` colors, the board has `q^2 + 1` rows and `q^4` T placements.

1. Each free cell gets a one-hot tuple of `q` Boolean variables constrained so exactly one is true. Cell assignments therefore correspond one-to-one with colorings extending the prefix.
2. For each unused pattern `p` and compatible open placement `w`, a variable `y[w,p]` is defined by a biconditional to the conjunction of the four required cell colors (after substituting any fixed cells). Each cell assignment forces a unique value for every `y[w,p]`.
3. For each unused pattern, a clause requires it to appear at some open placement. Because the number of unused patterns matches the number of open placements and every placement takes one pattern, every unused pattern must appear exactly once. A redundant clause per placement also requires one of its unused patterns to hold.
4. Optional redundant at-most-one (AMO) constraints strengthen propagation without changing the model count: pairwise constraints add no variables, tree constraints define auxiliaries by equivalences, and binary-index constraints uniquely fix every index bit via the active occurrence guaranteed by the at-least-one clause.

With palette normalization, the default tree encoding of the unrestricted ternary board has 13,341 variables and 59,488 clauses; without occurrence AMO clauses it has 6,861 variables and 33,568 clauses.

`--palette-canonical` requires colors to make their first appearance in the order `0, 1, ..., q-1`. Because every valid board uses all `q` colors, this picks one board from each `q!`-element color-permutation orbit (multiply the count by `q!` to recover labeled boards; reflection is left untouched). This flag cannot be combined with a fixed prefix, since a prefix already fixes color labels.

`--orbit-canonical` breaks horizontal reflection too. It implies palette normalization and compares the board lexicographically against every reflected recoloring that fixes color 0 (two comparisons for `q = 3`, one for `q = 2`; any reflected recoloring that changes color 0 raises the apex and cannot be smaller). For each comparison, `e[i]` holds when the first `i` cells agree: `e[0]` is true, `e[i+1] iff e[i] and (cell[i] = perm(cell[mirror(i)]))`, and when `e[i]` is true, clauses forbid a larger left-hand cell. Every `e[i]` is uniquely forced, selecting the exact lexicographic minimum of each symmetry orbit.

For three colors, [`ExactSymmetry.lean`](../ExactSymmetry.lean) proves in Lean that every valid board has trivial stabilizer, and `twelve_distinct_images` in [`ExactOrbit.lean`](../ExactOrbit.lean) proves every orbit has size 12, so multiplying the orbit-normalized count by **12** gives the unrestricted labeled count (formalized for any exact orbit selector by `length_eq_twelve_mul_canonical` in the same file). For two colors the multiplier is **4** (checked by complete enumeration below), and for one color it is **1**. The full orbit-normalized ternary tree model has **13,543 variables and 62,090 clauses**.

`--independent-support` emits a DIMACS support of the first `q - 1` one-hot variables per cell. Because the last one-hot variable and all remaining variables are uniquely determined, projecting onto this support preserves the count.

## Reproduction

The generator and test suite use only Python's standard library. From the project root:

```sh
python experiments/exact_count_cnf.py --orbit-canonical --independent-support experiments/exact_count_ternary_orbit.cnf
experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 experiments/exact_count_ternary_orbit.cnf
```

The second command has no built-in timeout and has not finished on the unrestricted instance; wrap it in an external timeout for benchmarks. Ganak defaults to probabilistic hashing, so `--prob 0` is required for deterministic exact counting, with no approximate fallback. A timeout means the run is incomplete, not zero.

The cross-check suite runs all four occurrence encodings on six cases: one-color (1), unrestricted binary (168), palette-normalized binary (84), orbit-normalized binary (42), one fixed valid ternary board (1), and a prefix with a repeated pattern (0). All **24 checks passed**, counting over all Boolean variables without projection so any accidental auxiliary multiplicity would be caught.

We also checked the actual symmetry-breaking clauses on all 17,160 symmetry images of the **1,430 saved representatives** in `extended_seeds.json`, confirming that only the lexicographic minimum of each orbit passes (this checks those 1,430 seed orbits, not the millions of later splice products):

```sh
python experiments/exact_count_check.py --known-orbits
```

Output is in `exact_count_check.log`. The unrestricted binary count of 168 matches the separate cell-wise and row-wise programs in `sources/anc/`.

We also counted the published seven-row prefix C:

```sh
python experiments/exact_count_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support experiments/exact_count_prefix_C.cnf
experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 256 experiments/exact_count_prefix_C.cnf
```

Both encodings returned **2**, matching the published restricted count: 16.28 CPU seconds for the tree encoding (`exact_count_prefix_C.log`) and 25.50 CPU seconds for pairwise AMO (`exact_count_prefix_C_pairwise.log`), measured alongside other jobs rather than as an isolated benchmark.

Bounded runs on harder instances timed out without a count:
- Six-row prefix of seed 0 (independently known to have 138 completions): timed out at 60 wall seconds.
- Unrestricted ternary (palette-normalized): timed out at 120 wall seconds after 148,916 conflicts and 0 cache hits.
- Unrestricted ternary (orbit-normalized): timed out at 60.007 wall seconds (`exact_count_ternary_orbit_status.json`, `exact_count_ternary_orbit.log`, recording multiplier 12).

All processes exited cleanly or at their limits. Combined run records are in `exact_count_runs.json`. Regenerating the benchmark CNFs with the final generator matched every formula exactly apart from header comments.

## Counter provenance and scope

The local binary is the official [Ganak 2.9.0 Linux AMD64 release](https://github.com/meelgroup/ganak/releases/tag/release%2Fv2.9.0); deterministic `--prob 0` is documented at the [official repository](https://github.com/meelgroup/ganak).

- Release archive SHA-256: `a303febfa889d887771d9c97680ca83475987d39166c524f50e8d9d344655183`
- Extracted executable SHA-256: `e7a3c6a66377db349939ceb01c78783767fbca5a3ef3dad66cbc6cf11f2daf58`
- Reported Ganak revision: `f262be5374f312b4bf7c99c6cca26e51182158e5`

Both sit in `exact_count_tools/` as external experimental tools and are outside Lean's trusted computing base. The proof above justifies the encoding, while solver counts are external computations rather than Lean theorems.

Original published certificate data keep their attribution and licenses in `sources/README.txt`, and no earlier certificate files were modified.
