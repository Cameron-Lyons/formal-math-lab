# OEIS A026019: Mathar's three-term binomial recurrence

Consider the integer sequence defined by the difference of two binomial coefficients,

$$
a_n = \binom{3n}{n} - \binom{3n}{n - 3} \qquad (a_0, a_1, a_2, a_3, \ldots = 1, 3, 15, 83, \ldots),
$$

with binomial coefficients at negative lower indices taken to be zero ([OEIS A026019](https://oeis.org/A026019)). On 20 June 2013, R. J. Mathar conjectured in the OEIS that every term from $n = 2$ onward is locked to its two predecessors by a linear **three-term polynomial recurrence** (whose coefficients are cubic polynomials in $n$).

Here, `A026019.recurrence` proves in Lean 4 that for every natural number $n \ge 2$,

$$
-2(2n+3)(13n-9)(n+1)a_n
+ (499n^3 - 7n^2 - 120n - 54)a_{n-1}
- 3(3n-5)(37n-24)(3n-4)a_{n-2} = 0.
$$

*(Quick check at $n = 2$, using $a_0 = 1, a_1 = 3, a_2 = 15$: $-2(7)(17)(3) \cdot 15 + 3670 \cdot 3 - 3(1)(50)(2) \cdot 1 = -10{,}710 + 11{,}010 - 300 = 0$.)*

| Field | Summary |
| --- | --- |
| Problem | OEIS A026019, R. J. Mathar's three-term polynomial recurrence conjecture for $a(n) = \binom{3n}{n} - \binom{3n}{n-3}$ |
| Status | Proved in Lean 4 for all $n \ge 2$. |
| Main theorems | `A026019.recurrence` ([A026019.lean](A026019.lean)), `A026019.a_eq` ([A026019/Sequence.lean](A026019/Sequence.lean)) |
| Verification | `lake exe cache get && lake build && lake env lean Check.lean` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proof, standard axioms only) |
| Prior art | Checked 23 November 2026 and re-audited 26 November 2026: Georg Fischer's first-order recurrence in jOEIS (6 November 2026) algebraically implies the recurrence, and Robert Israel independently verified the conjecture via Maple on 24 November 2026 (MathSE `q/5156049`, OEIS A026019 rev. 30). This folder provides a checked Lean proof, not a claim of a first mathematical proof. See [PRIOR_ART.md](PRIOR_ART.md) and the [collection audit](../PRIOR_ART.md#binomial-recurrence-oeis-a026019). |

## How the proof works

**The big idea:** A difference of two binomial coefficients is awkward to substitute directly into a recurrence, *unless* we rewrite both terms as rational multiples of a single hypergeometric building block $B_n = \binom{3n}{n}$. Because consecutive values of $B_n$ differ only by a simple ratio of polynomials, all three terms $a_n, a_{n-1}, a_{n-2}$ collapse into explicit rational multiples of one base term — turning the entire recurrence into a routine polynomial identity.

1. **Collapse $a_n$ to a multiple of $B_n$:** Write $B_n = \binom{3n}{n}$. Applying the elementary binomial shift identity $\binom{N}{r-1} = \frac{r}{N - r + 1}\binom{N}{r}$ three times expresses $\binom{3n}{n-3}$ in terms of $B_n$ and gives, for all $n \ge 0$,

   $$
   a_n = \frac{(n+3)(7n^2 + 6n + 2)}{2(n+1)(2n+1)(2n+3)} B_n.
   $$

   *(Notably, this single rational prefactor also reproduces the edge cases $n = 0, 1, 2$ without needing separate cases.)*

2. **Link consecutive $B_n$'s by factorial cancellation:** Comparing $\binom{3(n+1)}{n+1}$ with $\binom{3n}{n}$ gives the first-order relation

   $$
   2(2n+1)(n+1) B_{n+1} = 3(3n+1)(3n+2) B_n.
   $$

3. **Clear denominators and verify algebraically:** Substituting these two identities at three consecutive indices, clearing all nonzero denominators, and normalizing the resulting polynomial with Lean's `ring` tactic proves the recurrence over $\mathbb{Q}$, and then lifts it back to $\mathbb{Z}$.

**Avoiding natural-number subtraction traps in Lean:** In Lean, subtracting `Nat` values truncates at zero (`1 - 3 = 0`), which would mistakenly evaluate $\binom{3}{1-3}$ as $\binom{3}{0} = 1$ instead of $0$. Instead, Lean defines the second term as $\binom{3n}{2n+3}$. By binomial symmetry, $\binom{3n}{2n+3}$ equals $\binom{3n}{n-3}$ for $n \ge 3$ and automatically evaluates to $0$ for $n < 3$ (since $2n + 3 > 3n$). `A026019.a_eq` proves this matches the guarded original formula, keeping the initial terms $1, 3, 15, 83$ intact.

## Files

* [A026019.lean](A026019.lean): the recurrence and its shifted form.
* [A026019/Sequence.lean](A026019/Sequence.lean): definition, initial values, and closed form.
* [A026019/BinomialStep.lean](A026019/BinomialStep.lean): factorial cancellation.
* [A026019/RecurrenceAlgebra.lean](A026019/RecurrenceAlgebra.lean): polynomial elimination.
* [Check.lean](Check.lean): axiom audit for the main results.
* [PRIOR_ART.md](PRIOR_ART.md): algebraic comparison with jOEIS and literature check.

## Check the proof

Lean and mathlib are pinned to v4.36.0 (`lake-manifest.json` pins exact commits). With `elan` installed, run from this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

You can skip the first command if the mathlib build cache is already present. The proof uses no `sorry`, `admit`, custom axioms, or `native_decide`; [Check.lean](Check.lean) reports only `propext`, `Classical.choice`, and `Quot.sound`.
