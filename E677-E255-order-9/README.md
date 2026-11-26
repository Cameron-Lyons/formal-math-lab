# Equation 677 at orders 9 and 10, and E677 -> E255

Lean 4 proofs for Equation 677 (`E677`) at orders 9 and 10 from the [Equational Theories Project](https://teorth.github.io/equational_theories/):

* Order 9 (`Nine.eq677_implies_eq255` in [Nine.lean](Nine.lean)): every 9-element magma satisfying Equation 677 also satisfies Equation 255.
* Order 10 (`Ten.no_model` and `Ten.eq677_implies_eq255` in [Ten.lean](Ten.lean)): no 10-element magma satisfies Equation 677, so `E677 => E255` holds vacuously at order 10.

Whether Equation 677 implies Equation 255 in every finite magma remains open. José Brox previously reported both the order-9 and order-10 results from unverified Mace4 searches (December 2024 and January 2025); this folder gives Lean 4 proofs for both.

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 677 and Equation 255, finite implication `E677 -> E255`, and finite magma spectrum of E677 at orders 9 and 10 |
| Laws | E677: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`; E255: `x = ((x ◇ x) ◇ x) ◇ x` |
| Status | Orders 9 and 10 proved in Lean 4 (formalizing Brox's Mace4 reports). General finite `E677 -> E255` remains open. |
| Main theorems | `Nine.eq677_implies_eq255` ([Nine.lean](Nine.lean)), `Ten.no_model` and `Ten.eq677_implies_eq255` ([Ten.lean](Ten.lean)) |
| Verification | `lake build` with `../E670-order-10` beside it (Lean 4.36.0; kernel-checked reduction + LRAT certificates replayed via `native_decide`) |
| Prior art | Checked 23-24 November 2026: both results formalize earlier Mace4 reports; no earlier Lean proof of order 10 was found. See [PRIOR_ART.md](../PRIOR_ART.md#e677-at-order-ten). |

## Order 9: E677 implies E255

Suppose a 9-element magma satisfies Equation 677, $x = y \star (x \star ((y \star x) \star y))$, and breaks Equation 255, $x = ((x \star x) \star x) \star x$. Label a failing element $0$. Scan the first row from left to right: whenever column $i$ has an output larger than $i+1$, swap its label with $i+1$. Each swap fixes all earlier labels and outputs, so we can assume $0\star i \le i+1$.

Represent the table by Boolean variables $T(r,c,v)$ meaning $r\star c=v$. Each cell has one value, and each value appears once per row because Equation 677 gives a preimage for every value and a surjection on a finite set is a permutation.

The two equations become rules on triples of entries:

| If the table contains | What follows |
| --- | --- |
| $y\star x=a$, $a\star y=b$, $x\star b=c$ | Equation 677 forces $y\star c=x$. |
| $0\star 0=a$, $a\star 0=b$, $b\star 0=0$ | Equation 255 holds at $0$, contradicting the choice of $0$. |

Lean proves that any counterexample satisfies these clauses and label bounds. The resulting formula has 729 variables and 65,152 clauses. Lean verifies a refutation of that formula, finishing the proof.

## Order 10: no 10-element magma satisfies E677

Suppose a 10-element table satisfies Equation 677. Equation 255 may hold everywhere, so we cannot pick $0$ as a failure of Equation 255. Instead, call an element $0$ if $x\star x\ne x$, or pick any element if every element satisfies $x\star x=x$. Normalize the first row to $0\star i\le i+1$ as before. The choice of $0$ adds one rule: if $0\star 0=0$, then $x\star x=x$ for every $x$.

The formula has 1,000 variables and 309,246 clauses. They encode unique cell values, permutation rows, $0\star i\le i+1$, the rule for $0$, and Equation 677 in three forms. The extra two forms follow because rows are permutations and help the solver:

| If the table contains | What follows |
| --- | --- |
| $y\star x=a$, $a\star y=b$, $x\star b=c$ | $y\star c=x$, by Equation 677. |
| $y\star x=a$, $a\star y=b$, $y\star c=x$ | $x\star b=c$, canceling row $y$. |
| $y\star x=a$, $x\star b=c$, $y\star c=x$ | $a\star y=b$, canceling rows $y$ and $x$. |

A single refutation would be too large to check (the solver needs roughly 15 million conflicts in total), so the work is split into 709 cases. Each case fixes the first row and, for harder rows, up to three entries of the first column. The cases live in [Ten/Cases.lean](Ten/Cases.lean) in 81 groups.

The case list is not trusted. Lean checks one certificate per case (no solution in that case) and one covering certificate (no solution outside all cases). [scripts/cases.py](scripts/cases.py) generated the split by refining each case until CaDiCaL refuted it in at most 60,000 conflicts, omitting easy cases refuted in under 1,000 conflicts so the covering certificate handles them.

The element naming, table encoding, and case-split machinery come from the neighboring [Equation 670 project](../E670-order-10/), which handles 10-element tables of the same shape. This directory imports them and adds only the parts specific to Equation 677.

| File | Contents |
| --- | --- |
| [Laws.lean](Laws.lean) | The two equations (`E677` and `E255`). |
| [Nine.lean](Nine.lean) | The order-9 proof (`Nine.eq677_implies_eq255`). |
| [Ten/Formula.lean](Ten/Formula.lean) | Permutation rows, Equation 677 in three forms, the CNF formula, and the proof that every normalized E677 table satisfies it. |
| [Ten/Cases.lean](Ten/Cases.lean) | The 709 cases, generated by [scripts/cases.py](scripts/cases.py). |
| `Ten/Part/`, [Ten/Parts.lean](Ten/Parts.lean) | One three-line module per group plus their summary, generated via `../E670-order-10/scripts/parts.sh 81 Ten`. |
| [Ten.lean](Ten.lean) | The theorems `Ten.no_model` and `Ten.eq677_implies_eq255`. |

## Verify

Run `lake build` in this directory with Lean 4.36.0. The [Equation 670 project](../E670-order-10/) must sit beside it, as it does in this repository.

For order 9, Lean runs its bundled CaDiCaL solver to build an LRAT certificate and replays it with the standard library's verified checker. For order 10 it does the same for every case plus the covering certificate (710 checks in all). Certificates are not stored in the repository. Because replay uses `native_decide`, Lean's native compiler and runtime are inside the trust boundary; the algebra, relabeling, and CNF translation are kernel-checked.

On an 8-core machine the order-10 build took under 4 minutes and wrote about 3.7 GB under `.lake` (mostly certificate text). Lake builds the 81 case modules in parallel across available cores. Order 9 takes under a minute.

After building, inspect the theorems and their axioms with:

```sh
printf '%s\n' 'import Nine' 'import Ten' '#check Nine.eq677_implies_eq255' \
  '#check Ten.no_model' '#print axioms Nine.eq677_implies_eq255' \
  '#print axioms Ten.no_model' | lake env lean --stdin
```

Both depend on `propext`, `Classical.choice`, and `Quot.sound`. Order 9 adds one native-evaluation axiom; order 10 adds 82 (one for each of the 81 case modules and one for the covering certificate). There are no admitted lemmas.

Optionally, `lake env lean --run ExportCNF.lean > nine.cnf` exports the exact order-9 CNF formula for an external SAT checker. For order 10, `python3 scripts/cases.py` builds the formula from the equations with no shared Lean code, runs CaDiCaL on every case, and rewrites [Ten/Cases.lean](Ten/Cases.lean).

## Earlier work

José Brox reported the order-9 case in December 2024 from a Mace4 search ([report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914)).

For order 10, Brox reported on 22 December 2024 that no 10-element table satisfies Equation 677 while breaking Equation 255, and on 12 January 2025 that no 10-element table satisfies Equation 677 at all (after 39 hours of Mace4). Rudi Schneider reported in November 2025 that his search program finds every Equation 677 table through size 11, and the ICARM database lists no 10-element tables ([first report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#490346469), [second report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#493229385), [Schneider](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558558838), [ICARM database](https://eq677.icarm.cloud/size/10)).

Two 2026 reports describe SAT refutations of the weaker statement (no 10-element table satisfies Equation 677 and breaks Equation 255) with DRAT certificates checked by `drat-trim`. Neither publishes its certificates or gives a Lean proof ([Issue 1464](https://github.com/teorth/equational_theories/issues/1464), [mission page](https://prove2.me/missions/Equational_Magmas%3A_E677_%E2%86%92_E255_(finite_case))).

The order-10 theorem here gives a Lean-checked proof of Brox's second report rather than a new mathematical result. We found no earlier Lean proof of it, and the Lean spectrum catalogue in a fork of the Equational Theories Project still lists order 10 as undecided for Equation 677. See the [order-9 audit](../PRIOR_ART.md#e677-implies-e255-at-order-nine) and [order-10 audit](../PRIOR_ART.md#e677-at-order-ten).
