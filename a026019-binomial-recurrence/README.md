# OEIS A026019: Mathar's three-term binomial recurrence — Lean 4 proof

This Lean 4 project proves the three-term polynomial recurrence listed as a conjecture by R. J. Mathar (20 June 2013) in [OEIS A026019](https://oeis.org/A026019). For the integer sequence

$$
a_n = \binom{3n}{n} - \binom{3n}{n - 3} \qquad (a_0, a_1, a_2, a_3, \ldots = 1, 3, 15, 83, \ldots),
$$

with binomial coefficients at negative lower indices taken to be zero, `A026019.recurrence` proves for every natural number $n \ge 2$:

$$
-2(2n+3)(13n-9)(n+1)a_n
+ (499n^3 - 7n^2 - 120n - 54)a_{n-1}
- 3(3n-5)(37n-24)(3n-4)a_{n-2} = 0.
$$

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **OEIS A026019** (`A026019`), R. J. Mathar's three-term polynomial recurrence conjecture for `a(n) = C(3n, n) - C(3n, n-3)` (`1, 3, 15, 83, ...`) |
| **Status** | **Proved in Lean 4 for all $n \ge 2$.** |
| **Main Lean theorems** | `A026019.recurrence` ([A026019.lean](A026019.lean)), `A026019.a_eq` ([A026019/Sequence.lean](A026019/Sequence.lean)) |
| **Verification** | `lake exe cache get && lake build && lake env lean Check.lean` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proof, standard axioms only) |
| **Prior-art status** | Checked **23 November 2026**: no earlier explicit proof located, but Georg Fischer's first-order recurrence in jOEIS (6 November 2026) algebraically implies this recurrence. This project claims a checked Lean proof, not a first mathematical proof. See [PRIOR_ART.md](PRIOR_ART.md) and [collection audit](../PRIOR_ART.md#binomial-recurrence-oeis-a026019). |

## Proof overview

Write $B_n = \binom{3n}{n}$. Three applications of the elementary binomial step identity give, for all $n \ge 0$,

$$
a_n = \frac{(n+3)(7n^2 + 6n + 2)}{2(n+1)(2n+1)(2n+3)} B_n.
$$

Factorial cancellation gives the first-order relation

$$
2(2n+1)(n+1) B_{n+1} = 3(3n+1)(3n+2) B_n.
$$

Substitute these identities at three consecutive indices, clear the nonzero denominators, and normalize the resulting polynomial with `ring`. The proof works over $\mathbb{Q}$ and transfers the resulting equality to $\mathbb{Z}$.

In Lean, the sequence defines the second term as $\binom{3n}{2n+3}$. By binomial symmetry this equals $\binom{3n}{n-3}$ when $n \ge 3$ and is automatically $0$ when $n < 3$. The theorem `A026019.a_eq` proves equivalence to the guarded original formula, so natural-number subtraction does not alter the initial terms $1, 3, 15, 83$.

## Files

* [A026019.lean](A026019.lean): the exact recurrence and its shifted form.
* [A026019/Sequence.lean](A026019/Sequence.lean): definition, initial values, and closed form.
* [A026019/BinomialStep.lean](A026019/BinomialStep.lean): factorial cancellation.
* [A026019/RecurrenceAlgebra.lean](A026019/RecurrenceAlgebra.lean): polynomial elimination.
* [Check.lean](Check.lean): axiom audit for the main results.
* [PRIOR_ART.md](PRIOR_ART.md): detailed algebraic comparison with jOEIS and literature check.

## Check the proof

Lean and mathlib are pinned to **v4.36.0** (`lake-manifest.json` pins exact commits). With Elan installed, run from this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

The first command downloads mathlib's compiled cache and can be skipped when dependencies are already built. The proof uses no `sorry`, `admit`, custom axioms, or `native_decide`; [Check.lean](Check.lean) reports only `propext`, `Classical.choice`, and `Quot.sound`.
