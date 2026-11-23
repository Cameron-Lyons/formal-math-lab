# A026019: a proved binomial recurrence

This Lean 4 project proves the three-term recurrence listed as a conjecture in
[OEIS A026019](https://oeis.org/A026019), attributed there to R. J. Mathar
(June 20, 2013).

**Research status:** an earlier explicit proof of this exact recurrence was not
located, but historical priority is unverified. A first-order recurrence that
implies it was already implemented in jOEIS on November 6, 2026. This project
claims a checked Lean proof, not a first mathematical proof. See the
[prior-art audit](PRIOR_ART.md).

For

\[
a_n=\binom{3n}{n}-\binom{3n}{n-3},
\]

where binomial coefficients with a negative lower index are zero, the theorem
`A026019.recurrence` proves, for every natural number \(n\ge2\),

\[
-2(2n+3)(13n-9)(n+1)a_n
+(499n^3-7n^2-120n-54)a_{n-1}
-3(3n-5)(37n-24)(3n-4)a_{n-2}=0.
\]

The recurrence is an equality in the integers. The sequence starts
\(1,3,15,83\); these values are also proved in Lean.

## Proof

Write \(B_n=\binom{3n}{n}\). Three applications of the elementary binomial
step identity give, for all \(n\ge0\),

\[
a_n=\frac{(n+3)(7n^2+6n+2)}{2(n+1)(2n+1)(2n+3)}B_n.
\]

Factorial cancellation gives

\[
2(2n+1)(n+1)B_{n+1}=3(3n+1)(3n+2)B_n.
\]

Substitute these identities at three consecutive indices, clear the nonzero
denominators, and normalize the resulting polynomial with `ring`. The proof
works over the rationals and transfers the resulting equality to the integers.

The definition uses \(\binom{3n}{2n+3}\) for the second term. Binomial symmetry
makes this equal to \(\binom{3n}{n-3}\) when \(n\ge3\), and it is automatically
zero when \(n<3\). The theorem `A026019.a_eq` proves the equivalence to the
guarded original formula, so natural-number subtraction does not change the
initial terms.

## Files

- [A026019.lean](A026019.lean): the exact recurrence and its shifted form.
- [Sequence.lean](A026019/Sequence.lean): definition, initial values, and closed form.
- [BinomialStep.lean](A026019/BinomialStep.lean): factorial cancellation.
- [RecurrenceAlgebra.lean](A026019/RecurrenceAlgebra.lean): polynomial elimination.
- [Check.lean](Check.lean): axiom reports for the main results.

## Check the proof

Lean and mathlib are pinned to **v4.36.0**; `lake-manifest.json` pins the full
dependency revisions. With Elan installed, run from this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

The first command downloads mathlib's compiled cache and can be skipped when
the dependencies are already built. The proof uses no `sorry`, `admit`, custom
axioms, or `native_decide`. The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for the recurrence.
