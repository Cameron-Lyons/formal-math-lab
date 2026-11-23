# A176755: Mathar's five-term recurrence

This Lean 4 project proves the recurrence conjectured by R. J. Mathar in
[OEIS A176755](https://oeis.org/A176755), starting from the nonlinear definition

\[
a_0=1,\qquad a_1=3,\qquad
a_{n+1}=\sum_{p=0}^{n}a_pa_{n-p}-2\quad(n\ge1).
\]

The result, for every integer \(n\ge4\), is

\[
(n+1)a_n+2(1-3n)a_{n-1}+(n+3)a_{n-2}
+2(10n-33)a_{n-3}+16(4-n)a_{n-4}=0.
\]

## Prior work and attribution

This is an independently developed Lean formalization of a result already
covered by earlier work; no mathematical novelty or first-formalization claim
is made.

[OEIS A176604](https://oeis.org/A176604) records a proof for the related family
by Georg Fischer, dated January 26, 2020, and links
[his derivation](https://oeis.org/A176604/a176604_2.txt).
The attachment could not be fetched during this check (HTTP 403), so the
attribution here relies on the OEIS record and the published recurrence.
Fischer's [A176755 implementation from January 2020](https://github.com/archmageirvine/joeis/blob/e072e99444a75d6f2a1d48100932e999994d5a48/src/irvine/oeis/a176/A176755.java)
explicitly uses

\[
(n+1)a_n+(2-7n)a_{n-1}+(7n-5)a_{n-2}+(19n-68)a_{n-3}
+(150-36n)a_{n-4}+(16n-80)a_{n-5}=0.
\]

To check its implication for the present result, let \(R_n\) be the left-hand
side of Mathar's five-term formula. Direct expansion shows that Fischer's
six-term expression is \(R_n-R_{n-1}\). The defining initial values give
\(R_4=260-330+28+42=0\), so the earlier recurrence implies \(R_n=0\) for all
\(n\ge4\). The continued “Conjecture” label in A176755 does not establish
that the mathematical problem remained open.

## Formal statements

- `A176755.a` is an explicitly defined integer sequence, using well-founded
  recursion. `a_zero`, `a_one`, and `a_recurrence` verify the defining conditions.
- `A176755.mathar_of_recurrence` proves the result for **any** integer sequence
  satisfying those conditions.
- `A176755.mathar` specializes the theorem to `A176755.a`.

The entire proof works over the integers. The `4 ≤ n` hypothesis ensures that natural-number
subtraction in the sequence indices agrees with the displayed formula.
The generating-function identity is proved from the recurrence, not assumed.

## Proof

Work in the ring of formal power series over the integers, and put
\(F=\sum_{n\ge0}a_nx^n\). The defining recurrence says the coefficients of
\(F-xF^2\) are \(1,2,-2,-2,\ldots\). Therefore

\[
(1-x)(F-xF^2)=1+x-4x^2.
\]

Differentiate the quadratic equation and eliminate \(F^2\). This gives

\[
x(1-6x+x^2+20x^3-16x^4)F'
+(1-4x+5x^2-6x^3)F=1+2x-13x^2+8x^3.
\]

For \(n\ge4\), the coefficient on the right is zero. On the left it is

\[
(n+1)a_n+[-6(n-1)-4]a_{n-1}+[(n-2)+5]a_{n-2}
+[20(n-3)-6]a_{n-3}-16(n-4)a_{n-4},
\]

which is exactly Mathar's recurrence. No convergence, analytic differentiation,
or square-root construction is used.

For an explicit check of the elimination, write
\(H=x(1-x)F^2-(1-x)F+1+x-4x^2\) and let \(E\) be the left side minus the
right side of the differential equation. Lean checks the single polynomial identity

\[
(1-2xF)E=(-1-4x^2+32x^3)H
-x(1-5x-4x^2+16x^3)H'.
\]

Since \(H=H'=0\) and \(1-2xF\) has constant coefficient \(1\), cancellation
in the integral domain \(\mathbb Z[[x]]\) gives \(E=0\).

The main Lean proof now just composes these three steps:

```lean
  have hq := quadratic_of_recurrence b h0 h1 hrec
  have hd := differential_of_quadratic (generatingFunction b) hq
  simpa using coefficients_of_differential (generatingFunction b) hd n hn
```

## Files

- `A176755/Sequence.lean`: the integer sequence and its defining recurrence.
- `A176755/GeneratingFunction.lean`: recurrence to quadratic equation.
- `A176755/Differential.lean`: differentiation and polynomial elimination.
- `A176755/Coefficients.lean`: coefficient extraction.
- `A176755.lean`: the final theorems, composing the three proof steps.
- `Check.lean`: theorem signatures and axiom audit.

## Reproduce

The project pins Lean and mathlib to `v4.36.0`; `lake-manifest.json` pins the
dependency commits. With Lean's `elan` toolchain manager installed, run from
this directory:

```sh
lake exe cache get Mathlib.RingTheory.PowerSeries.Derivative Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.NatAntidiagonal Mathlib.Tactic.LinearCombination Mathlib.Tactic.NormNum
lake build
lake env lean Check.lean
```

The local `.lake/packages` symlink reuses the machine's existing mathlib cache;
it is not part of the source project. A fresh checkout downloads the pinned
dependencies through Lake.

## Verification

`lake build` and `lake env lean Check.lean` both succeed. The final theorems'
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, the
standard Lean foundations used by mathlib. There are no `sorry` declarations,
additional axioms, or `native_decide` proofs.
