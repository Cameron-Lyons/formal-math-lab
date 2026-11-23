# Fixed cellwise color gauges and spatial factor symmetries

**Theorem.** Assign a fixed permutation `π_p ∈ S₃` to each of the 100 cells.
If applying these permutations takes every valid ternary T board to a valid
board, then all 100 permutations are the same.

Thus fixed row-dependent, diagonal-dependent, or arbitrary cell-dependent
palette permutations yield no additional universal symmetry. This statement
does **not** classify transformations chosen after inspecting the board,
transformations acting only within a particular boundary fiber, or arbitrary
permutations of the set of valid boards.

A finite set of **322 valid test boards** already forces the conclusion. The
proof uses a 161-board rank certificate and exact color counts on three anchor
boards. It does not assume that the known board families are exhaustive.

- [Explicit certificate](exact_structure_gauge_certificate.json)
- [Standalone checker and deterministic generator](exact_structure_gauge.py)
- [Checker audit](exact_structure_gauge_audit.json)
- [Separate independent audit](exact_structure_gauge_independent_audit.json)

```sh
python experiments/exact_structure_gauge.py
python experiments/exact_structure_gauge.py --regenerate /tmp/exact_structure_gauge_reproduced.json
cmp experiments/exact_structure_gauge_certificate.json /tmp/exact_structure_gauge_reproduced.json
```

Regeneration reproduced the certificate byte for byte. Its SHA-256 is
`963fe8a5371697b6856db05fc6388e763cb99abcdaeb63d75bac56cb00aac7c9`.

## The finite rank argument on one role

Let `S_L` be the 81 cells used as lower-left cells of T placements. Each is
used in that role exactly once. On a valid board each color occurs 27 times
in `S_L`.

Work over `F₂`. Associate to a board its lifted one-hot vector

```
x(B) = (1, [B(p)=a] for p∈S_L and a∈{0,1,2}).
```

There are 244 coordinates. Every such vector satisfies the following 84
homogeneous relations:

```
x_* + x_(p,0) + x_(p,1) + x_(p,2) = 0     for each of 81 cells p;
x_* + Σ_p x_(p,a) = 0                     for each of three colors a.
```

The first equations express one-hot membership. The second use that 27 is
odd. There is exactly one dependency among these relations: the sum of the
81 local equations equals the sum of the three global equations. To see
there are no others, write a linear combination with coefficients `α_p`
and `β_a`. Its `(p,a)` coefficient is `α_p+β_a`; vanishing of all such
coefficients forces every `α_p` and `β_a` to be equal. Thus the relation
space has dimension 83 and the allowed lifted space has dimension 161.

The certificate contains **161 valid boards whose vectors have rank 161**.
Consequently these known relations constitute the entire annihilator of
their span. Both the checker and an independent audit verify that rank using
all 244 one-hot coordinates. Each board is independently checked by
Cartesian-coordinate enumeration of all 81 T placements.

Now fix an output color `b`. Define

```
u_(p,a) = [π_p(a)=b].
```

Because each `π_p` is a permutation, `u_p` is a one-hot vector of length
three. If the transformed test boards remain valid, their lower-left color
counts are also odd. Therefore the coefficient vector `(1,u)` annihilates
all 161 lifted board vectors. By the rank result, for suitable `α_p,β_a`,

```
u_(p,a) = α_p + β_a   in F₂.
```

If two cells had different `α` values, their one-hot vectors would be
bitwise complements. A complement of a length-three one-hot vector has two
ones and cannot itself be one-hot. Hence all `α_p` are equal, and the
preimage of `b` under `π_p` is the same at every cell of `S_L`. Applying this
argument to all three output colors shows that all `π_p` on `S_L` agree.

### Explicit XOR certificates instead of trusting elimination

The supplied data also give 160 explicit XOR identities. Eliminate each
color-2 coordinate using the local one-hot relation and keep the constant
coordinate plus the color-0 and color-1 indicators. This produces a compressed
163-coordinate vector.

For each non-reference cell and each retained color, an even-size selection
of the 161 board vectors XORs to the vector supported exactly at that
cell/color coordinate and the reference cell's corresponding coordinate.
The checker directly evaluates every supplied selection. These 160 vectors
are visibly independent; adding any lifted board vector gives rank 161.
Thus the rank conclusion can be verified from the explicit identities,
without relying solely on a Gaussian-elimination implementation.

## Covering the other nineteen cells

Horizontal reflection `R` preserves validity and swaps the lower-left and
lower-right role sets. Conjugate the cellwise map by `R`. Applying the same
argument to the reflected test boards shows that the original permutations
also agree throughout `S_R`.

The two role sets intersect in 64 cells, so their common permutations are
the same permutation `π`. Their union contains 98 cells. The only exceptions
are flattened cell 0, the apex, and flattened cell 2, the center of row 1.

The anchor board has color 0 at both exceptions. Its three cyclic recolorings
give valid boards whose two exceptional colors are both `c`, for each
`c∈{0,1,2}`. Compare the cellwise-transformed anchor with its globally
`π`-recolored version. They agree everywhere except possibly at those two
cells. Both have exactly 27 occurrences of each color in the top role,
which contains both exceptions. Therefore, **over the integers**,

```
e_(π_apex(c)) + e_(π_center(c)) = 2 e_(π(c)).
```

Both exceptional images must equal `π(c)`. This holds for all three values
of `c`, finishing the proof.

This final step deliberately uses integer color counts. Parity alone would
allow both exceptional cells to move together and would not suffice.

The 161 boards, their reflections, and the three anchor recolorings form
322 distinct boards; the anchor recolorings are already in that union.
Thus any fixed cellwise permutation taking this finite test set into valid
boards is necessarily global. Conversely every global palette permutation
preserves validity.

## Uncolored T-incidence automorphisms are also only reflection and identity

This section classifies cell relocations that map the collection of T
placements to itself, even without assuming a uniform permutation of the
four roles.

Connect two placements when they intersect in exactly two cells. The resulting
graph is the disjoint union of nine paths, of sizes `1,3,…,17`: two-cell
intersections occur exactly between neighboring placements in the same row.
An incidence automorphism must preserve each component, since their sizes
are distinct. It can therefore only reverse each path or leave it fixed.

The intersections between neighboring placement rows force the reversal
choices to agree. A placement `W_(r,j)` intersects a placement `W_(r+1,k)`
precisely when `k∈{j,j+1,j+2}`. For `r≥2`, reversing exactly one of the two
rows destroys this relation, while reversing both preserves it. Hence all
non-singleton paths have the same orientation choice. Finally, all 100 cells
have distinct placement-incidence sets, so their images are determined by
the induced placement permutation.

There are consequently only two cell relocations: identity and horizontal
reflection. The checker constructs the incidence system from coordinates,
verifies the nine paths and 100 distinct cell-incidence sets, and tests all
256 possible row-orientation choices. Exactly the identity and reflection
extend to cell permutations.

As a second check, the role-set intersection sizes are:

| | T | L | M | R |
|---|---:|---:|---:|---:|
| T | 81 | 64 | 64 | 64 |
| L | 64 | 81 | 72 | 64 |
| M | 64 | 72 | 81 | 72 |
| R | 64 | 64 | 72 | 81 |

Their only role permutations are identity and exchanging L with R.

Combining an incidence-preserving cell relocation with fixed cellwise palette
permutations therefore gives exactly the already known `S₃ × C₂`, of order
12. This does not classify spatial permutations that preserve the solution
set without preserving the T-incidence system.

## What endpoint-pair equality does contract exactly

There is an exact matching identity behind the lower-pair balance condition.
It does not by itself produce an additional board symmetry.

For row `r`, let `s_r` and `e_r` be its starting and ending lower pairs. Put

```
M_(r,s) = [e_r = s_s],
d_v = number of starting pairs equal to v.
```

The permanent of this 9×9 matrix counts bijections matching row ends to
compatible row starts. Such a matching exists exactly when the start and
end multisets agree. If they agree, each pair value `v` allows `d_v!`
independent matchings. Hence

```
[start multiset = end multiset] = permanent(M) / ∏_v d_v!.
```

Equivalently, the numerator is a sum over the 9! row permutations, with a
product of nine local endpoint-equality indicators. For a fixed boundary
multiset `d`, this replaces the global balance condition by compatible
cycle gluings with the constant normalization `∏_v d_v!`.

The anchor has starting-pair multiplicities `00:3, 01:2, 10:1, 12:2, 22:1`,
and exactly `3!·2!·2!=24` compatible matchings. The checker verifies the
permanent by subset dynamic programming. The matching count is not constant
across valid boards: the selected certificate boards realize counts
`4,6,8,12,16,24`. In particular, extended seed 0 with unchanged color names
has 24 matchings, while extended seed 1 has only 4. Decorating boards with
all endpoint matchings and dividing by one fixed factor would therefore
miscount; the boundary-dependent normalization is necessary.

This is an exact contraction, but its cycle components do not factor the
full board count: row `r`'s top-color word must still equal the actual word
in row `r−1`, which can belong to another gluing cycle. The prescribed row
lengths must also remain fixed. Ignoring these conditions counts independent
path systems rather than boards. The earlier
[structural note](exact_structure.md) gives explicit failures of the
corresponding local Euler-walk identification.

The unrestricted exact count is not computed by this certificate or identity.
All explicit board data retain their source provenance in the certificate;
see the project's [source notices](../sources/README.txt).
