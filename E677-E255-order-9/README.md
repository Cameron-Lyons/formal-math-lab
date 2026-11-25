# Equation 677 at orders 9 and 10, and E677 -> E255

Lean 4 proofs for Equation 677 (`E677`) at orders 9 and 10 from the [Equational Theories Project](https://teorth.github.io/equational_theories/):

* Order 9 (`Nine.eq677_implies_eq255` in [Nine.lean](Nine.lean)): every 9-element magma satisfying Equation 677 also satisfies Equation 255.
* Order 10 (`Ten.no_model` and `Ten.eq677_implies_eq255` in [Ten.lean](Ten.lean)): no 10-element magma satisfies Equation 677, so `E677 => E255` holds vacuously at order 10.

Whether Equation 677 implies Equation 255 in every finite magma remains open. Both the order-9 and order-10 statements were previously reported from unverified Mace4 searches by José Brox (December 2024 and January 2025); this folder provides Lean 4 proofs.

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 677 and Equation 255, finite implication `E677 -> E255`, and finite magma spectrum of E677 at orders 9 and 10 |
| Laws | E677: `x = y ◇ (x ◇ ((y ◇ x) ◇ y))`; E255: `x = ((x ◇ x) ◇ x) ◇ x` |
| Status | Orders 9 and 10 proved in Lean 4 (formalizing Brox's Mace4 reports). General finite `E677 -> E255` remains open. |
| Main theorems | `Nine.eq677_implies_eq255` ([Nine.lean](Nine.lean)), `Ten.no_model` and `Ten.eq677_implies_eq255` ([Ten.lean](Ten.lean)) |
| Verification | `lake build` with `../E670-order-10` beside it (Lean 4.36.0; kernel-checked reduction + LRAT certificates replayed via `native_decide`) |
| Prior art | Checked 23-24 November 2026: both results formalize earlier Mace4 reports; no earlier Lean proof of order 10 located. See [PRIOR_ART.md](../PRIOR_ART.md#e677-at-order-ten). |

## Order 9: E677 implies E255

Suppose a 9-element magma satisfies Equation 677, $x = y \star (x \star ((y \star x) \star y))$, and fails Equation 255, $x = ((x \star x) \star x) \star x$. Label a failing element $0$. In the first row, scan the columns from left to right. If the output in column $i$ is larger than $i+1$, swap its label with $i+1$. Each swap fixes the names and outputs at all earlier columns. We may therefore assume $0\star i \le i+1$.

Now represent a table by Boolean variables $T(r,c,v)$ meaning $r\star c=v$. Each cell has exactly one value. Each value occurs once per row because Equation 677 supplies a preimage for every value, and a surjection on a finite set is a permutation.

The two equations translate directly into rules about three known entries:

| If the table contains | What follows |
| --- | --- |
| $y\star x=a$, $a\star y=b$, $x\star b=c$ | Equation 677 requires $y\star c=x$. |
| $0\star 0=a$, $a\star 0=b$, $b\star 0=0$ | Equation 255 holds at $0$, contradicting the choice of $0$. |

Lean proves that a counterexample would satisfy these rules and the label bounds. The resulting formula has 729 variables and 65,152 clauses. Lean verifies a refutation of that formula, completing the contradiction.

## Order 10: no 10-element magma satisfies E677

Suppose a 10-element table satisfies Equation 677. Equation 255 may hold everywhere in it, so the element $0$ cannot be taken to be a failure of Equation 255. Instead, label as $0$ an element with $x\star x\ne x$ if there is one, and any element otherwise. The first row is then put in the form $0\star i\le i+1$ as before. The choice of $0$ gives one more rule: if $0\star 0=0$ then $x\star x=x$ for every $x$.

The formula has 1,000 variables and 309,246 clauses. They say that every cell has one value, that every row is a permutation, that $0\star i\le i+1$, the rule about $0$, and Equation 677 in three forms. The second and third forms follow because the rows are permutations, and they help the solver.

| If the table contains | What follows |
| --- | --- |
| $y\star x=a$, $a\star y=b$, $x\star b=c$ | $y\star c=x$, by Equation 677. |
| $y\star x=a$, $a\star y=b$, $y\star c=x$ | $x\star b=c$, cancelling row $y$. |
| $y\star x=a$, $x\star b=c$, $y\star c=x$ | $a\star y=b$, cancelling rows $y$ and $x$. |

A single refutation would be too large to check: the solver needs about fifteen million conflicts in all. The work is therefore divided into 709 cases. A case fixes the first row, and for the harder rows it also fixes up to three entries of the first column. The cases are listed in [Ten/Cases.lean](Ten/Cases.lean), in 81 groups.

The list of cases is not trusted. Lean checks one certificate per case, showing that the formula has no solution in that case, and one more certificate showing that no solution of the formula lies outside all the cases. [scripts/cases.py](scripts/cases.py) chose the cases: it divides a case further until CaDiCaL refutes it within 60,000 conflicts, and it leaves out the cases refuted in under 1,000, which the last certificate covers.

The naming of the elements, the table encoding, and the case-by-case refutation are those of the neighbouring [Equation 670 project](../E670-order-10/), which treats 10-element tables of the same kind. The order-10 proof imports them; this directory adds only what is specific to Equation 677.

| File | Contents |
| --- | --- |
| [Laws.lean](Laws.lean) | The two equations (`E677` and `E255`). |
| [Nine.lean](Nine.lean) | The order-9 proof (`Nine.eq677_implies_eq255`). |
| [Ten/Formula.lean](Ten/Formula.lean) | Rows are permutations; Equation 677 in three forms; the formula, and the proof that a table satisfying Equation 677 satisfies it once its elements are named as above. |
| [Ten/Cases.lean](Ten/Cases.lean) | The 709 cases. Written by [scripts/cases.py](scripts/cases.py). |
| `Ten/Part/`, [Ten/Parts.lean](Ten/Parts.lean) | One three-line module per group, and their summary. Written by the Equation 670 project's `scripts/parts.sh`, run here as `../E670-order-10/scripts/parts.sh 81 Ten`. |
| [Ten.lean](Ten.lean) | The theorems `Ten.no_model` and `Ten.eq677_implies_eq255`. |

## Verify

Run `lake build` in this directory with Lean 4.36.0. The [Equation 670 project](../E670-order-10/) must be present beside it, as it is in this repository.

For order 9, Lean uses its bundled CaDiCaL solver to generate an LRAT certificate and replays it with the standard library's verified checker. For order 10 it does the same once per case and once for the covering certificate, 710 times in all. The certificates are not stored in the repository. Replay uses `native_decide`, so this computation trusts Lean's native compiler and runtime. The algebra, relabelling, and translation to Boolean clauses are kernel-checked.

On an 8-core machine the order-10 build took under four minutes and wrote about 3.7 GB under `.lake`, almost all of it certificate text. Lake builds the 81 case modules in parallel, as many at a time as there are cores. Order 9 takes under a minute.

After a Lake build, inspect the theorems and their axioms with

```sh
printf '%s\n' 'import Nine' 'import Ten' '#check Nine.eq677_implies_eq255' \
  '#check Ten.no_model' '#print axioms Nine.eq677_implies_eq255' \
  '#print axioms Ten.no_model' | lake env lean --stdin
```

Both depend on the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`. Order 9 adds one native-evaluation axiom. Order 10 adds 82: one for each of the 81 case modules and one for the covering certificate. There are no admitted lemmas.

The optional command `lake env lean --run ExportCNF.lean > nine.cnf` exports the exact order-9 search formula for use with an independent SAT checker. For order 10, `python3 scripts/cases.py` writes the formula from the equations, shares no code with the Lean files, and reports CaDiCaL's refutation of every case; it also rewrites [Ten/Cases.lean](Ten/Cases.lean).

## Earlier work

José Brox reported the order-9 case in December 2024 from a Mace4 search. [Report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#487358914)

For order 10, Brox reported on 22 December 2024 that no 10-element table satisfies Equation 677 and breaks Equation 255, and on 12 January 2025 that no 10-element table satisfies Equation 677 at all, after 39 hours of Mace4. Rudi Schneider reported in November 2025 that his own search program finds every Equation 677 table through size 11, and the ICARM database of Equation 677 tables lists none with ten elements ([first report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#490346469), [second report](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#493229385), [Schneider](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/FINITE.3A.20677.20-.3E.20255.html#558558838), [ICARM database](https://eq677.icarm.cloud/size/10)).

Two reports from 2026 describe SAT refutations of the weaker statement, that no 10-element table satisfies Equation 677 and breaks Equation 255, with DRAT certificates accepted by `drat-trim`. Neither publishes its certificates, and neither is a Lean proof ([Issue 1464](https://github.com/teorth/equational_theories/issues/1464), [mission page](https://prove2.me/missions/Equational_Magmas%3A_E677_%E2%86%92_E255_(finite_case))).

Thus the order-10 theorem here is not a new mathematical result; it is a Lean-checked proof of Brox's second report. No earlier Lean proof of it was located, and the Lean spectrum catalogue kept in a fork of the Equational Theories Project lists order 10 as undecided for Equation 677. See the [order-9 audit](../PRIOR_ART.md#e677-implies-e255-at-order-nine) and [order-10 audit](../PRIOR_ART.md#e677-at-order-ten).
