# Fixed cellwise color gauges and spatial factor symmetries

**Theorem.** Assign a fixed permutation `π_p ∈ S₃` to each of the 100 cells.
If applying those permutations maps every valid ternary T board to a valid
board, then all 100 permutations are identical.

Fixed row-dependent, diagonal-dependent, or cell-dependent palette swaps
therefore give no extra universal symmetry. This theorem does **not** rule out
board-dependent transformations, symmetries inside a single boundary fiber, or
arbitrary bijections on the set of valid boards.

A finite test set of **322 valid boards** already forces the result, using a
161-board rank certificate and integer color counts on three anchor boards,
without assuming that known board families are exhaustive.

- [Explicit certificate](exact_structure_gauge_certificate.json)
- [Standalone checker and deterministic generator](exact_structure_gauge.py)
- [Checker audit](exact_structure_gauge_audit.json)
- [Separate independent audit](exact_structure_gauge_independent_audit.json)

```sh
python experiments/exact_structure_gauge.py
python experiments/exact_structure_gauge.py --regenerate /tmp/exact_structure_gauge_reproduced.json
cmp experiments/exact_structure_gauge_certificate.json /tmp/exact_structure_gauge_reproduced.json
```

Regeneration reproduces the certificate byte for byte, with SHA-256
`963fe8a5371697b6856db05fc6388e763cb99abcdaeb63d75bac56cb00aac7c9`.

## The finite rank argument on one role

Let `S_L` be the 81 cells used as lower-left cells of T placements; each cell
in `S_L` appears in that role once, and on a valid board each color appears 27
times in `S_L`.

Over `F₂`, map each board `B` to its lifted one-hot vector of 244 coordinates:

```
x(B) = (1, [B(p)=a] for p∈S_L and a∈{0,1,2}).
```

Every valid board vector obeys 84 homogeneous linear equations:

```
x_* + x_(p,0) + x_(p,1) + x_(p,2) = 0     for each of 81 cells p;
x_* + Σ_p x_(p,a) = 0                     for each of three colors a.
```

The first 81 equations express one-hot encoding, and the last 3 use the fact
that 27 is odd. There is one linear dependency among them: the sum of the 81
cell equations equals the sum of the 3 color equations. There are no others: in
any linear combination with weights `α_p` and `β_a`, the `(p, a)` entry is
`α_p + β_a`, so vanishing everywhere forces all `α_p` and `β_a` to agree. The
relation space therefore has dimension 83, leaving a 161-dimensional allowed
subspace.

The certificate gives **161 valid boards whose lifted vectors have rank 161**,
so those 84 equations generate the full annihilator of their span. Both the
checker and the independent audit check this rank across all 244 one-hot
coordinates and verify each board directly by Cartesian enumeration of all 81 T
placements.

Now fix an output color `b` and put

```
u_(p,a) = [π_p(a)=b].
```

Because each `π_p` is a permutation, every `u_p` is a length-3 one-hot vector.
If applying `π_p` keeps all 161 test boards valid, their lower-left counts of
color `b` remain odd, so `(1, u)` annihilates all 161 lifted vectors. By the
rank result, there exist `α_p, β_a ∈ F₂` with

```
u_(p,a) = α_p + β_a   in F₂.
```

If two cells had different `α` values, their one-hot vectors would be bitwise
complements, which is impossible because the complement of a length-3 one-hot
vector has weight 2. Hence all `α_p` are equal, so `π_p^(-1)(b)` is the same at
every cell in `S_L`. Repeating this for all three output colors `b` forces all
`π_p` on `S_L` to coincide.

### Explicit XOR certificates instead of trusting elimination

The certificate also stores 160 explicit XOR identities. Eliminating each
color-2 bit via the cell's one-hot equation leaves a compressed 163-coordinate
vector (the constant bit plus color-0 and color-1 indicators).

For every non-reference cell and each of the two kept colors, an even-size
subset of the 161 board vectors XORs to the vector supported on just that
cell-color bit and the reference cell's matching bit. The checker evaluates all
160 XORs directly. Because those 160 vectors are visibly linearly independent,
adding any single lifted board vector yields rank 161, allowing verification
without relying only on Gaussian elimination code.

## Covering the other nineteen cells

Horizontal reflection `R` preserves board validity and swaps `S_L` with the
lower-right role set `S_R`. Conjugating the cellwise gauge by `R` and applying
the same argument to the reflected test boards forces all `π_p` on `S_R` to
agree as well.

Because `S_L` and `S_R` overlap in 64 cells, both roles share the same single
permutation `π`. Their union covers 98 cells, leaving only cell 0 (the apex)
and cell 2 (the center of row 1).

The anchor board has color 0 at both missing cells, so its three cyclic
recolorings give valid boards with color `c` at both cells for each
`c ∈ {0, 1, 2}`. Comparing the cellwise-transformed anchor with its globally
`π`-recolored version, they agree everywhere except possibly at cells 0 and 2.
Both cells belong to the top role, where each color must appear 27 times. Over
the integers,

```
e_(π_apex(c)) + e_(π_center(c)) = 2 e_(π(c)),
```

so both `π_apex(c)` and `π_center(c)` must equal `π(c)` for every `c`. This
step needs exact integer counts; parity alone would let both cells move
together.

The 161 boards, their reflections, and the three anchor recolorings (already
inside that union) give 322 distinct boards. Any fixed cellwise permutation
preserving validity on these 322 boards must be global, and every global color
permutation preserves validity.

## Uncolored T-incidence automorphisms are also only reflection and identity

We also classify all cell permutations that map the set of 81 T placements to
itself, without assuming any uniform permutation of the four roles.

Connect two placements by an edge whenever they share exactly two cells. That
graph is a disjoint union of nine paths of lengths `1, 3, ..., 17`, since
two-cell overlaps occur only between adjacent placements in the same row. Every
path has a distinct size, so an incidence automorphism must preserve each path,
either fixing it or reversing it.

Intersections between neighboring rows lock all row orientations together:
placement `W_(r,j)` meets `W_(r+1,k)` if and only if `k ∈ {j, j+1, j+2}`. For
`r ≥ 2`, reversing just one of the two rows breaks that adjacency while
reversing both keeps it, so all paths of length > 1 must share the same
orientation. Finally, all 100 cells lie in distinct sets of placements, so the
placement permutation uniquely fixes the cell permutation.

That leaves only two spatial relocations: the identity and horizontal
reflection. The checker builds the incidence graph from coordinates, confirms
the nine paths and 100 distinct cell-incidence sets, and tests all 256
row-orientation choices; only identity and reflection extend to cell
permutations.

As a cross-check, the pairwise role-set overlap sizes are:

| | T | L | M | R |
|---|---:|---:|---:|---:|
| T | 81 | 64 | 64 | 64 |
| L | 64 | 81 | 72 | 64 |
| M | 64 | 72 | 81 | 72 |
| R | 64 | 64 | 72 | 81 |

Only the identity and swapping `L` with `R` preserve this matrix.

Combining incidence-preserving cell relocations with fixed cellwise color
gauges therefore yields only the known group `S₃ × C₂` of order 12. (This does
not classify spatial permutations that preserve valid boards without preserving
the set of T placements.)

## What endpoint-pair equality does contract exactly

The lower-pair flow balance condition has an exact matching identity, though it
does not add a new board symmetry.

For each row `r`, let `s_r` and `e_r` be its starting and ending lower pairs,
and define

```
M_(r,s) = [e_r = s_s],
d_v = number of starting pairs equal to v.
```

The permanent of this 9×9 matrix counts bijections gluing row ends to matching
row starts. A matching exists if and only if the start and end multisets agree,
and when they agree each pair value `v` admits `d_v!` matchings:

```
[start multiset = end multiset] = permanent(M) / ∏_v d_v!.
```

Equivalently, the numerator sums a product of nine local endpoint-equality
indicators over all `9!` row permutations. For a fixed boundary multiset `d`,
that rewrites global balance as compatible cycle gluings normalized by the
constant `∏_v d_v!`.

For the anchor board, starting-pair counts are `00:3, 01:2, 10:1, 12:2, 22:1`,
giving `3! * 2! * 2! = 24` matchings (verified via subset dynamic programming).
That count is not constant across boards: certificate boards take values
`4, 6, 8, 12, 16, 24`, with extended seed 0 having 24 matchings and extended
seed 1 having 4. Weighting boards by all endpoint matchings and dividing by one
global constant would miscount; the boundary-dependent factor `∏_v d_v!` is
required.

Even as an exact identity, these gluing cycles do not factor the board count:
row `r`'s top word must still match row `r−1` (which may lie in another cycle),
and the row lengths stay fixed. Dropping those constraints counts independent
path systems rather than boards. See [the structural note](exact_structure.md)
for explicit failures of the related local Euler-walk model.

This certificate and identity do not compute the unrestricted exact count. All
board data keep their source provenance in the certificate; see
[source notices](../sources/README.txt).
