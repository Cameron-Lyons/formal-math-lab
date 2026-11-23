# Exact model-counting experiment

The unrestricted ternary count was **not obtained**. This experiment supplies
a parsimonious Boolean model and checks it against smaller exact counts. It is
an executable route to the count, not evidence that the full calculation will
finish within practical resources.

## Encoding and proof of count preservation

For `q` colors, the board has `q^2+1` rows and `q^4` T placements.

1. Each unfixed cell has a one-hot list of `q` Boolean variables, constrained
   to contain exactly one true variable. Thus cell assignments correspond
   bijectively to board colorings extending the prefix.
2. For every still-unused pattern `p` and compatible open placement `w`, a
   Boolean variable `y[w,p]` is defined by a biconditional to the conjunction
   of the four required cell colors. Fixed cells are substituted first.
   These variables have exactly one extension for every cell assignment.
3. For each unused pattern, a clause requires it to occur at some open
   placement. The number of unused patterns equals the number of open
   placements, and each placement has exactly one pattern. Consequently,
   these clauses force every unused pattern to occur exactly once. A
   redundant clause at each placement requires one of its unused patterns.
4. Optional redundant at-most-one constraints improve propagation. Pairwise
   constraints introduce no variables. Tree constraints define every
   auxiliary by a Boolean equivalence. The binary-index encoding defines
   every index bit through the selected occurrence; the at-least-one clause
   guarantees that such an occurrence exists. All variants therefore retain
   the same number of models.

The default tree encoding has 13,341 variables and 59,488 clauses for the
unrestricted ternary problem with palette normalization. Without occurrence
AMO clauses there are 6,861 variables and 33,568 clauses. Neither size is a
runtime guarantee.

`--palette-canonical` requires first appearances of the colors to have the
order 0, 1, ..., q-1. Every valid board uses all colors, so this selects exactly
one coloring from each orbit of the `q!` global color permutations. Multiply
that model count by `q!` to recover the labeled count. No reflection quotient
is imposed by this option. This option rejects a fixed prefix because the
prefix's color labels must then retain their prescribed meaning.

`--orbit-canonical` also removes horizontal reflection. It implies palette
normalization and compares the board lexicographically with every recolored
reflection whose recoloring fixes 0. There are two such comparisons for three
colors and one for two colors. All other reflected recolorings have a larger
apex, so cannot be smaller than the normalized board.

For each comparison, `e[i]` is true exactly when the first `i` cells agree.
The initial variable is fixed true; subsequent variables are defined by
`e[i+1] iff e[i] and (cell[i] = perm(cell[mirror(i)]))`. If `e[i]` is true,
clauses prohibit a larger left-hand cell. Every comparison auxiliary therefore
has a unique assignment. Together with palette normalization, these clauses
select precisely the lexicographic minimum of the full symmetry orbit.

For ternary boards the unrestricted stabilizer theorem in
[`ExactSymmetry.lean`](../ExactSymmetry.lean) proves that no nonidentity
color-permutation/reflection symmetry fixes a valid board. The ordinary
group-action corollary makes every orbit size 12, so multiply this normalized
model count by **12** to obtain the unrestricted labeled count. The analogous
binary multiplier is **4**, checked by the complete binary enumeration below.
For the degenerate one-color case the multiplier is 1. The ternary tree model
with full orbit normalization has **13,543 variables and 62,090 clauses**.

`--independent-support` optionally emits a DIMACS support consisting of the
first `q-1` one-hot variables at each cell. The last variable is their negated
disjunction and all remaining variables are functional auxiliaries. Hence
projecting onto this support also preserves the count; the hint is optional.

## Reproduction

The generator and its checks use only Python's standard library. Run from
the project root:

```sh
python experiments/exact_count_cnf.py --orbit-canonical --independent-support experiments/exact_count_ternary_orbit.cnf
experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 512 experiments/exact_count_ternary_orbit.cnf
```

The second command is deliberately unbounded: no completed unrestricted
result is supplied. Apply an external time limit when only benchmarking.
Ganak's default mode permits probabilistic hashing; `--prob 0` is necessary
here for deterministic exact counting. No approximate-counting fallback is
enabled. Any timeout is an incomplete computation, not a numerical result.

The cross-check suite runs all four occurrence encodings against six cases:
one-color boards (1), unrestricted binary boards (168), palette-normalized
binary boards (84), fully orbit-normalized binary boards (42), one completely
fixed valid ternary board (1), and a prefix with a repeated pattern (0).
All **24 checks passed**. The suite counts
all Boolean variables without a projection hint, so it also detects
auxiliary-variable multiplicities on these cases.

The actual normalization clauses were additionally checked against every
symmetry image of all **1,430 saved representatives** in `extended_seeds.json`:
17,160 images, with exactly the explicit lexicographic minimum accepted in
each orbit. This checks those 1,430 explicit seed orbits; it does not expand
the millions of cap-tail products in the later certificates.

```sh
python experiments/exact_count_check.py --known-orbits
```

The result is recorded in `exact_count_check.log`. The unrestricted binary
count 168 agrees with the separate cell-wise and row-wise programs supplied
in the repository's `sources/anc/` directory.

The seven-row published prefix C was also independently counted:

```sh
python experiments/exact_count_cnf.py --prefix-json sources/anc/certificates.json --prefix-name C --independent-support experiments/exact_count_prefix_C.cnf
experiments/exact_count_tools/ganak --prob 0 --arjun 0 --puura 0 --td 0 --maxcache 256 experiments/exact_count_prefix_C.cnf
```

The tree encoding returned exactly **2** in 16.28 CPU seconds, matching the
published restricted count. Pairwise AMO also returned **2**, in 25.50 CPU
seconds. These timings are single observations with concurrent experiments,
not a controlled benchmark. See `exact_count_prefix_C.log` and
`exact_count_prefix_C_pairwise.log`.

The six-row prefix from seed 0 did not complete within 60 wall seconds.
Its independently known count is 138; that count was not reproduced by this
bounded model-counting run. The unrestricted ternary trial did not complete
within 120 wall seconds. Its last periodic statistics reported 148,916
conflicts and zero cache hits. All benchmark processes were terminated by
their specified time limits or completed normally; none remains running.

A subsequent unrestricted trial using full orbit normalization also timed
out, after 60.007 wall seconds, without an exact count. Its command, timeout
status, and multiplier 12 are recorded in
`exact_count_ternary_orbit_status.json`; the solver log is
`exact_count_ternary_orbit.log`. The combined experiment results are recorded
in `exact_count_runs.json`. Preserved benchmark CNFs were regenerated with
the final generator and matched their original formulas exactly, ignoring
descriptive comments.

## Counter provenance and scope

The downloaded local counter is the official
[Ganak 2.9.0 Linux AMD64 release](https://github.com/meelgroup/ganak/releases/tag/release%2Fv2.9.0).
The project documents deterministic `--prob 0` at its
[official repository](https://github.com/meelgroup/ganak).

Release archive SHA-256:
`a303febfa889d887771d9c97680ca83475987d39166c524f50e8d9d344655183`.

Extracted executable SHA-256:
`e7a3c6a66377db349939ceb01c78783767fbca5a3ef3dad66cbc6cf11f2daf58`.

The executable reports Ganak source revision
`f262be5374f312b4bf7c99c6cca26e51182158e5`.
The archive and executable are in `exact_count_tools/`; they are external
experimental tools and are not added to the Lean certificate or its trusted
proof. The correctness argument above establishes the reduction; the
benchmark counts are computations by an external solver, not Lean theorems.

Original published certificate data retain their attribution and licenses
in `sources/README.txt`. No prior certificate files were changed.
