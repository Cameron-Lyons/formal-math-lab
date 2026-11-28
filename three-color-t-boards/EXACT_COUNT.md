# Exact-count structural theorems

How many valid labeled three-color T boards exist in total? Let $N$ denote the exact unrestricted count of 3-colorings of the 100-cell ziggurat $Z_9$ in which all $3^4 = 81$ ordered upright T patterns occur once. The best certified lower bound proved here is $N \ge 45{,}083{,}592$ ([SplicePalCertificates.lean](SplicePalCertificates.lean)); the exact unrestricted total remains open.

This document summarizes the kernel-checked Lean 4 structural theorems proved for `TBoards.Valid` in pursuit of $N$.

## 1. Global orbit-size-12 theorem

Every valid ternary board — not just the millions of boards in our splicing certificates — has **exactly 12 distinct images** under the 6 color permutations and horizontal reflection. In particular, $N$ is guaranteed to be a multiple of 12.

**Proof summary.** Because a board is valid, reading its 81 T windows defines a **bijection** between the 81 geometric placements and the 81 color patterns. Any symmetry fixing the board must fix the same number of placements and patterns:

* **Without reflection:** all **81** placements are fixed, whereas only the identity fixes all 81 patterns (a color swap fixes 1 pattern; a 3-cycle fixes 0).
* **With horizontal reflection:** reflection fixes the **9** center-column placements (one per lower row $r = 1, \ldots, 9$), whereas on patterns a reflection combined with a color permutation fixes **27, 3, or 0** patterns — never 9.

Thus the stabilizer is always trivial, and the 12 symmetries produce 12 distinct valid boards.

**Lean formalization.** [ExactSymmetry.lean](ExactSymmetry.lean) proves `TBoards.ExactSymmetry.stabilizer_trivial` inside Lean's kernel from `Valid b` alone. From the same hypothesis, [ExactOrbit.lean](ExactOrbit.lean) proves:

* `TBoards.ExactOrbit.twelve_distinct_images`: `orbit b` has length 12, contains no duplicates, and consists entirely of valid boards.
* `TBoards.ExactOrbit.length_eq_twelve_mul_canonical`: any duplicate-free list of valid boards closed under all 12 symmetries has length 12 times the sublist picked by any selector choosing one canonical image per orbit.

```sh
lake build ExactSymmetry ExactOrbit
```

Both modules build cleanly using only `propext`, `Classical.choice`, and `Quot.sound`.

## 2. Exact reduced system of pattern counts (marginals)

Write $N(a, b, c, d)$ for the number of times pattern $(a, b, c, d)$ appears on a board. Validity asks that all 81 counts equal 1. An **equivalent** system imposes:

1. **16 binary-cube equations:** $N(a, b, c, d) = 1$ for every $(a, b, c, d) \in \{0, 1\}^4$.
2. **65 selected three-coordinate margins equal to 3:** for the margin summing over coordinate $j \in \{0, 1, 2, 3\}$, keep only triples whose entries *before* $j$ lie in $\{0, 1\}$ ($27 + 18 + 12 + 8 = 65$ margins).

By induction on the number of `2`s in a pattern, locating its first `2` determines its count from two counts with fewer `2`s and one selected margin summing to 3.

[ExactMarginals.lean](ExactMarginals.lean) proves this exact equivalence to `TBoards.Valid` for every board.

**Sharpness (binary-cube conditions cannot be dropped).** Triple margins alone do not characterize validity: [MarginalCounterexample.lean](MarginalCounterexample.lean) verifies inside Lean's kernel an explicit well-formed board whose **108** triple margins all equal 3 and which satisfies 15 of the 16 binary-cube equations, yet doubles `(1, 1, 1, 1)`.

```sh
lake build ExactMarginals MarginalCounterexample
```

## 3. Exact parity and modular saturation

**A board is valid if and only if every one of the 81 patterns occurs an odd number of times** — and more generally, if and only if every count is $\equiv 1 \pmod m$ for any integer $m > 1$. Each congruence forces every count to be at least 1, and having only 81 placements forces all 81 counts to equal 1.

[ExactParity.lean](ExactParity.lean) proves `TBoards.ExactParity.valid_iff_present`, `valid_iff_odd`, and `valid_iff_congruent_one` for arbitrary $m > 1$.

```sh
lake build ExactParity
```

## 4. Exact $\mathbb{F}_3$ power-moment equivalence

Encoding the three colors directly as $\mathbb{F}_3 = \{0, 1, 2\}$ and summing each nonzero monomial over $\{0, 1, 2\}^4$ across all 81 T placements gives 80 power-sum equations: every nonzero exponent tuple sums to `0` over $\mathbb{F}_3$ except `(2, 2, 2, 2)`, whose target is `1`. Inverting the finite transform shows these 80 equations force every pattern count to be $\equiv 1 \pmod 3$, which by modular saturation is equivalent to `TBoards.Valid`.

[ExactNativeMoments.lean](ExactNativeMoments.lean) proves this exact equivalence inside Lean's kernel using only standard axioms.

```sh
lake build ExactNativeMoments
```
