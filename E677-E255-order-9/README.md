# Equation 677 at orders 9 and 10, and E677 -> E255

A **finite magma** of order $n$ is a set of $n$ elements with an $n \times n$ multiplication table $a \star b$, with no associativity or commutativity assumed. One of the remaining open questions in the [Equational Theories Project](https://teorth.github.io/equational_theories/) asks whether **Equation 677** implies **Equation 255** in every finite magma:

* **Equation 677 (`E677`):** $x = y \star \bigl(x \star ((y \star x) \star y)\bigr)$ — in ETP notation, `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`.
* **Equation 255 (`E255`):** $x = ((x \star x) \star x) \star x$ — in ETP notation, `x = ((x ◇ x) ◇ x) ◇ x`.

While the general finite implication `E677 -> E255` remains **open**, this Lean 4 project provides mechanically verified proofs for orders **9** and **10**:

* **Order 9** (`Nine.eq677_implies_eq255` in [Nine.lean](Nine.lean)): every 9-element magma satisfying Equation 677 also satisfies Equation 255.
* **Order 10** (`Ten.no_model` and `Ten.eq677_implies_eq255` in [Ten.lean](Ten.lean)): **no** 10-element magma satisfies Equation 677 at all, so `E677 => E255` holds vacuously at order 10.

José Brox previously reported both results from unverified Mace4 searches (December 2024 and January 2025); this directory formalizes both in Lean 4 using kernel-checked reductions and verified SAT/LRAT refutations.

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 677 and Equation 255, finite implication `E677 -> E255`, and finite magma spectrum of E677 at orders 9 and 10 |
| Laws | E677: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`; E255: `x = ((x ◇ x) ◇ x) ◇ x` |
| Status | Orders 9 and 10 proved in Lean 4 (formalizing Brox's Mace4 reports). General finite `E677 -> E255` remains open. |
| Main theorems | `Nine.eq677_implies_eq255` ([Nine.lean](Nine.lean)), `Ten.no_model` and `Ten.eq677_implies_eq255` ([Ten.lean](Ten.lean)) |
| Verification | `lake build` with `../E670-order-10` beside it (Lean 4.36.0; kernel-checked reduction + LRAT certificates replayed via `native_decide`) |
| Prior art | Checked 23-24 November 2026: both results formalize earlier Mace4 reports; no earlier Lean proof of order 10 was found. |

## Order 9: E677 implies E255

**Proof strategy.** Suppose for contradiction that a 9-element magma obeys Equation 677 while breaking Equation 255 at some element. We relabel the elements canonically to crush symmetry without discarding any counterexample, translate the table into a Boolean CNF formula, and check a SAT/LRAT refutation proving the formula has no solution.

1. **Canonical labeling:** Label a failing element of Equation 255 as $0$. Scan row $0$ from left to right: whenever column $i$ has $0 \star i > i + 1$, swap the labels $i + 1$ and $0 \star i$. Because both swapped labels exceed $i$ and every earlier entry $0 \star j$ ($j < i$) is already at most $j + 1 \le i$, each swap leaves all earlier labels and outputs intact. Afterward, $0 \star i \le i + 1$ for every $i$.
2. **Permutation rows:** For any fixed row $y$, Equation 677 displays every element $x$ as $y \star (\text{something})$, so row $y$ is surjective. On a finite set, a surjection is a bijection—every row contains each value once.
3. **Boolean encoding:** Introduce $9^3 = 729$ Boolean variables $T(r, c, v)$ meaning "$r \star c = v$". Add clauses enforcing unique cell values, permutation rows, the label bounds $0 \star i \le i + 1$, and the two equational laws:

| If the table contains | What follows |
| --- | --- |
| $y \star x = a$, $a \star y = b$, $x \star b = c$ | Equation 677 forces $y \star c = x$. |
| $0 \star 0 = a$, $a \star 0 = b$, $b \star 0 = 0$ | Equation 255 holds at $0$, contradicting the choice of $0$. |

Lean's kernel proves that every normalized counterexample satisfies all **65,152 clauses** on these **729 variables**. Lean then verifies an LRAT refutation of the formula, completing `Nine.eq677_implies_eq255`.

## Order 10: no 10-element magma satisfies E677

At order 10 we prove the stronger statement that *no* 10-element table satisfies Equation 677 at all.

**Adapting the normalization.** Because Equation 255 might hold everywhere in a hypothetical model, we can no longer pick $0$ as a failure of Equation 255. Instead, name an element $0$ if it is non-idempotent ($x \star x \ne x$), or pick any element if every element satisfies $x \star x = x$. Normalize row $0$ to $0 \star i \le i + 1$ exactly as before. Our choice of $0$ contributes one extra rule: if $0 \star 0 = 0$, then $x \star x = x$ for every $x$.

**Three-way clauses from permutation rows.** Encoding the $10 \times 10$ table uses $10^3 = 1,000$ Boolean variables and **309,246 clauses**: unique cell values, permutation rows, $0 \star i \le i + 1$, the rule for $0$, and Equation 677 written in three equivalent forms. Because every row is a permutation (giving left cancellation), the two extra forms follow immediately from the law and substantially speed up SAT propagation:

| If the table contains | What follows |
| --- | --- |
| $y \star x = a$, $a \star y = b$, $x \star b = c$ | $y \star c = x$, by Equation 677. |
| $y \star x = a$, $a \star y = b$, $y \star c = x$ | $x \star b = c$, canceling row $y$. |
| $y \star x = a$, $x \star b = c$, $y \star c = x$ | $a \star y = b$, canceling rows $y$ and $x$. |

**Case-split refutation (709 cases + 1 covering check).** A single refutation would be too large to replay (the solver needs roughly 15 million conflicts in total), so we split the search into **709 cases** stored in [Ten/Cases.lean](Ten/Cases.lean) across **81 groups**. Each case fixes the first row and, for harder rows, up to three entries of the first column.

The case list is **not** trusted: Lean verifies one LRAT certificate per case (ruling out solutions inside that case) plus one covering certificate (ruling out solutions outside all 709 cases). The split was generated by refining each case until CaDiCaL refuted it in at most 60,000 conflicts, omitting easy cases refuted in under 1,000 conflicts so the covering certificate handles them automatically.

**Shared infrastructure.** The element naming, table encoding, and case-split machinery are imported directly from the neighboring [Equation 670 project](../E670-order-10/), which handles 10-element tables of the same shape; this directory adds only the parts specific to Equation 677.

| File | Contents |
| --- | --- |
| [Laws.lean](Laws.lean) | The two equations (`E677` and `E255`). |
| [Nine.lean](Nine.lean) | The order-9 proof (`Nine.eq677_implies_eq255`). |
| [Ten/Formula.lean](Ten/Formula.lean) | Permutation rows, Equation 677 in three forms, the CNF formula, and the proof that every normalized E677 table satisfies it. |
| [Ten/Cases.lean](Ten/Cases.lean) | The 709 cases. |
| `Ten/Part/`, [Ten/Parts.lean](Ten/Parts.lean) | One three-line module per group plus their summary. |
| [Ten.lean](Ten.lean) | The theorems `Ten.no_model` and `Ten.eq677_implies_eq255`. |

## Verify

Run `lake build` in this directory with Lean 4.36.0. The [Equation 670 project](../E670-order-10/) must sit beside it, as it does in this repository.

**Trust boundary.** During `lake build`, Lean runs its bundled CaDiCaL solver to generate LRAT certificates on the fly (1 for order 9; 710 for order 10, covering all 709 cases plus the covering check) and replays every certificate with the standard library's formally verified checker. Certificates are not stored in the repository. Because replay runs via `native_decide`, Lean's native compiler and runtime sit inside the trust boundary; the algebra, relabeling, and CNF translation are checked directly by Lean's kernel, and neither the solver nor the case split is trusted.

On an 8-core machine the order-10 build took under 4 minutes and wrote about 3.7 GB under `.lake` (mostly certificate text). Lake builds the 81 case modules in parallel across available cores. Order 9 takes under a minute.

After building, inspect the theorems and their axioms with:

```sh
printf '%s\n' 'import Nine' 'import Ten' '#check Nine.eq677_implies_eq255' \
  '#check Ten.no_model' '#print axioms Nine.eq677_implies_eq255' \
  '#print axioms Ten.no_model' | lake env lean --stdin
```

Both depend on `propext`, `Classical.choice`, and `Quot.sound`. Order 9 adds one native-evaluation axiom; order 10 adds 82 (one for each of the 81 case modules and one for the covering certificate). There are no admitted lemmas.

## Earlier work

José Brox reported the order-9 case in December 2024 from a Mace4 search ([report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914)).

For order 10, Brox reported on 22 December 2024 that no 10-element table satisfies Equation 677 while breaking Equation 255, and on 12 January 2025 that no 10-element table satisfies Equation 677 at all (after 39 hours of Mace4). Rudi Schneider reported in November 2025 that his search program finds every Equation 677 table through size 11, and the ICARM database lists no 10-element tables ([first report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#490346469), [second report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#493229385), [Schneider](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558558838), [ICARM database](https://eq677.icarm.cloud/size/10)).

Two 2026 reports describe SAT refutations of the weaker statement (no 10-element table satisfies Equation 677 and breaks Equation 255) with DRAT certificates checked by `drat-trim`. Neither publishes its certificates or gives a Lean proof ([Issue 1464](https://github.com/teorth/equational_theories/issues/1464), [mission page](https://prove2.me/missions/Equational_Magmas%3A_E677_%E2%86%92_E255_(finite_case))).

The order-10 theorem here gives a Lean-checked proof of Brox's second report rather than a new mathematical result. We found no earlier Lean proof of it, and the Lean spectrum catalogue in a fork of the Equational Theories Project still lists order 10 as undecided for Equation 677.
