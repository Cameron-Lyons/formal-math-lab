# Four sparse cubic histogram consequences for the natural F₃ model

The [frozen natural-field model](exact_f3_math.md) admits four additional
redundant cubic generators with **574 terms total**, no auxiliary variables,
and no additional domain equations. They are exported separately; the base
model and its input bytes are unchanged.

The augmentation is [exact_f3_math_e3_constraints.json](exact_f3_math_e3_constraints.json),
SHA256 `6cef0fb4e6b3ccb80f17f7aebadfd02fd777d082e1dedb84cdf5d9786d408392`.
It pins the native base JSON SHA256
`fe1321842be3bf5bdb8ff91cd5b9c38017d542968fe27a8d5a8952e344564cc4`.

| Label | Original-cell polynomial | Terms in the 96 prefix variables |
|---|---|---:|
| `e3:T` | `e3(T)` | 158 |
| `e3:T:M` | `e3(T\M)−e3(M\T)` | 180 |
| `e3:M:L` | `e3(M\L)−e3(L\M)` | 86 |
| `e3:M:R` | `e3(M\R)−e3(R\M)` | 150 |

Every exported term has ordinary degree three and coefficient one or two in
F₃. There are no Frobenius partners: cubing does not give a new conjugate
equation on F₃ points.

## Validity and the available quadratic conditions

Each role on a valid board has 27 cells of each color `0,1,2`. Its elementary
generating polynomial is

```
∏cells(1+z t) = ((1+t)(1−t))^27 = (1−t²)^27 = 1−t^54
```

over F₃, so in particular `e3=0`.

The existing native moments already supply `p1=Σz=0` and `p2=Σz²=0` for
each role. Newton's degree-two identity is `2e2=p1²−p2`. After the unary
linear elimination this reads **`e2=p2` in F₃**. Thus the four role `e2`
conditions are already present in the base model; no characteristic-two
elementary equations are being imported.

## Exact role-difference certificate

Let `A,B` be two role sets, `C=A∩B`, `D=A\B`, `E=B\A`, and `s=e1(C)`.
The unary equations imply `e1(D)=e1(E)=−s`. Disjoint-union expansion then gives

```
e3(A)−e3(B)−e3(D)+e3(E) = s*(e2(A)−e2(B)).
```

The generator verifies this as an ordinary polynomial identity in the actual
signed prefix coordinates. Its right side is a combination of existing unary
quadratic power-moment generators. Therefore the exclusive-set equations in
the table are equivalent to the three role differences in `e3`. Together
with `e3(T)` they impose all four role `e3` conditions.

## Why the top equation is local

The first 81 cells in the Gray order form the top role. Write their colors as
`z_i=p_i−p_(i−1)`, with `p_0=p_81=0`. There is the polynomial identity

```
e3(z_1,…,z_81)
 = Σ_(i=1..79) (p_i²*p_(i+1) − p_i*p_(i+1)²).
```

One proof first works over the integer polynomial ring. Since `Σz_i=0`,
Newton's identity gives `3e3=Σz_i³`. Expanding the adjacent differences
telescopes the pure cubes and gives three times the displayed sum. Cancel
three over the integer polynomial ring, then reduce coefficients modulo three.
This does not divide by three inside F₃.

The 80 interior prefix variables remain distinct after the other unary
eliminations. Hence the 79 adjacent pairs give exactly 158 cubic monomials.
The implementation also independently computes `e3` from the generating
product and matches this formula term by term.

## Strength and scope of the extra equations

For a role-count triple summing to 81, the existing `e1=e2=0` conditions mean
all three counts are divisible by three. Write them as `3m_c`. The coefficient
`e3` is `m_1−m_2` modulo three. Its vanishing makes all three counts share a
common residue **0, 3, or 6 modulo 9**. It does not force residue zero alone.
The generator checks this equivalence on all 3403 count triples: 406 satisfy
the first two conditions, and 136 also satisfy `e3=0`.

After reduction modulo the retained field cubics, the base has 26 moment
generators of degree at most three. Their F₃ linear span has rank 26; adding
these four cubics raises the rank to 30. This is a statement about that linear
span, not about variable multiples or higher-degree cancellations.

The full native ideal is a product-of-fields quotient and already describes
exactly the valid boards. Each cubic above vanishes on those boards, so it is
already in that radical ideal. Adding the four generators leaves the ideal,
its quotient dimension, and the full labeled count unchanged. No prefix or
symmetry normalization is imposed.

[The checker](exact_f3_math_e3.py) also verifies all 161 existing valid boards.
[The audit](exact_f3_math_e3_audit.json) records the identities, degree counts,
rank check, histogram enumeration, and frozen hash. Reproduce without a solver:

```sh
python experiments/exact_f3_math_e3.py --check
```

No full basis computation or count is claimed here.
