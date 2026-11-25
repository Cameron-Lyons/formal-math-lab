# OEIS A176755: Mathar's five-term linear recurrence

Lean 4 proof of the five-term linear polynomial recurrence conjectured by R. J. Mathar in [OEIS A176755](https://oeis.org/A176755). Starting from the nonlinear convolution recurrence

$$
a_0 = 1, \qquad a_1 = 3, \qquad a_{n+1} = \sum_{p=0}^{n} a_p a_{n-p} - 2 \quad (n \ge 1)
$$

(initial terms $1, 3, 4, 15, 52, \ldots$), `A176755.mathar` proves for every integer $n \ge 4$:

$$
(n+1)a_n + 2(1-3n)a_{n-1} + (n+3)a_{n-2} + 2(10n-33)a_{n-3} + 16(4-n)a_{n-4} = 0.
$$

| Field | Summary |
| --- | --- |
| Problem | OEIS A176755, R. J. Mathar's five-term linear recurrence conjecture for $a_{n+1} = \sum_{p=0}^n a_p a_{n-p} - 2$ |
| Status | Proved in Lean 4 for all $n \ge 4$ (formalizing a result already covered by Georg Fischer's January 2020 recurrence). |
| Main theorems | `A176755.mathar`, `A176755.mathar_of_recurrence` in [A176755.lean](A176755.lean) |
| Verification | `lake exe cache get && lake build && lake env lean Check.lean` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proof, standard axioms only) |
| Prior art | Checked 23 November 2026: covered by Georg Fischer's January 2020 recurrence for OEIS A176604/A176755. No mathematical novelty or first-formalization claim is made. See [Prior work and attribution](#prior-work-and-attribution) and [PRIOR_ART.md](../PRIOR_ART.md#nonlinear-to-linear-recurrence-oeis-a176755). |

## Prior work and attribution

This is an independently developed Lean formalization of a result already covered by earlier work; no mathematical novelty or first-formalization claim is made.

[OEIS A176604](https://oeis.org/A176604) records a proof for 85 related sequences by Georg Fischer, dated 26 January 2020, and links [his derivation](https://oeis.org/A176604/a176604_2.txt) (which returned HTTP 403 during our check, so attribution relies on the OEIS record and published recurrence). Fischer's [A176755 implementation from January 2020](https://github.com/archmageirvine/joeis/blob/e072e99444a75d6f2a1d48100932e999994d5a48/src/irvine/oeis/a176/A176755.java) uses the six-term recurrence

$$
(n+1)a_n + (2-7n)a_{n-1} + (7n-5)a_{n-2} + (19n-68)a_{n-3} + (150-36n)a_{n-4} + (16n-80)a_{n-5} = 0.
$$

Let $R_n$ be the left-hand side of Mathar's five-term formula. Direct expansion shows that Fischer's six-term expression is $R_n - R_{n-1}$. Since the initial values give $R_4 = 260 - 330 + 28 + 42 = 0$, the earlier recurrence implies $R_n = 0$ for all $n \ge 4$. The continued "Conjecture" label in OEIS A176755 does not mean the mathematical problem remained open.

## Formal statements

* `A176755.a` is an integer sequence defined by well-founded recursion; `a_zero`, `a_one`, and `a_recurrence` verify the defining conditions.
* `A176755.mathar_of_recurrence` proves the five-term recurrence for any integer sequence satisfying those defining conditions.
* `A176755.mathar` specializes the theorem to `A176755.a`.

The proof works over $\mathbb{Z}$ (with `4 ≤ n` ensuring natural-number subtraction matches the displayed indices). The generating-function identity is proved from the recurrence rather than assumed.

## Proof overview

Work in the formal power series ring $\mathbb{Z}[[x]]$ with $F = \sum_{n \ge 0} a_n x^n$. The defining recurrence says that $F - xF^2$ has coefficients $1, 2, -2, -2, \ldots$, so

$$
(1 - x)(F - xF^2) = 1 + x - 4x^2.
$$

Differentiating this quadratic equation and eliminating $F^2$ gives the linear differential equation

$$
x(1 - 6x + x^2 + 20x^3 - 16x^4) F' + (1 - 4x + 5x^2 - 6x^3) F = 1 + 2x - 13x^2 + 8x^3.
$$

For $n \ge 4$, the coefficient of $x^n$ on the right is $0$, while on the left it is

$$
(n+1)a_n + [-6(n-1) - 4]a_{n-1} + [(n-2) + 5]a_{n-2} + [20(n-3) - 6]a_{n-3} - 16(n-4)a_{n-4},
$$

which is Mathar's recurrence. No convergence, analytic differentiation, or square-root construction is needed.

To check the elimination algebraically, put $H = x(1-x)F^2 - (1-x)F + 1 + x - 4x^2$ and let $E$ be the left side minus the right side of the differential equation. Lean verifies the polynomial identity

$$
(1 - 2xF) E = (-1 - 4x^2 + 32x^3) H - x(1 - 5x - 4x^2 + 16x^3) H'.
$$

Since $H = H' = 0$ and $1 - 2xF$ has constant term $1$, cancellation in the integral domain $\mathbb{Z}[[x]]$ gives $E = 0$. The main proof composes these three steps:

```lean
  have hq := quadratic_of_recurrence b h0 h1 hrec
  have hd := differential_of_quadratic (generatingFunction b) hq
  simpa using coefficients_of_differential (generatingFunction b) hd n hn
```

## Files

* [A176755/Sequence.lean](A176755/Sequence.lean): the integer sequence and its defining recurrence.
* [A176755/GeneratingFunction.lean](A176755/GeneratingFunction.lean): recurrence to quadratic power-series equation.
* [A176755/Differential.lean](A176755/Differential.lean): formal differentiation and polynomial elimination.
* [A176755/Coefficients.lean](A176755/Coefficients.lean): coefficient extraction.
* [A176755.lean](A176755.lean): final theorems composing the three steps.
* [Check.lean](Check.lean): theorem signatures and axiom audit.

## Reproduce

Lean and mathlib are pinned to v4.36.0 (`lake-manifest.json` pins exact commits). With `elan` installed, run from this directory:

```sh
lake exe cache get Mathlib.RingTheory.PowerSeries.Derivative Mathlib.Algebra.BigOperators.Fin Mathlib.Algebra.BigOperators.NatAntidiagonal Mathlib.Tactic.LinearCombination Mathlib.Tactic.NormNum
lake build
lake env lean Check.lean
```

Both `lake build` and `lake env lean Check.lean` succeed. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry`, custom axioms, or `native_decide`.
