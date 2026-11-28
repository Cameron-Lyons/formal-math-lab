# Equation 670 at order 10

A **finite magma** of order $n$ is a set of $n$ elements with an $n \times n$ multiplication table $a \star b$, with no associativity or commutativity assumed. In the [Equational Theories Project](https://teorth.github.io/equational_theories/), **Equation 670** (opposite-operation dual **Equation 2937**, obtained by transposing the table) is the law

$$
x = y \star \bigl(x \star ((x \star y) \star y)\bigr)
$$

for all $x, y$ — written in ETP notation as `x = y ◇ (x ◇ ((x ◇ y) ◇ y))`.

Models of Equation 670 exist at sizes 1, 4, 5, 9, 11, and every sufficiently large size, whereas sizes 2, 3, 6, 7, and 8 were already ruled out—leaving **order 10** as the smallest undecided size in the finite spectrum catalogue we checked. This Lean 4 project proves that **no 10-element magma satisfies Equation 670** (`E670.no_model_of_order_ten`).

## At a glance

| Field | Summary |
| --- | --- |
| Problem | Equational Theories Project Equation 670 (dual Equation 2937), finite magma spectrum at order 10 |
| Law | `x = y ◇ (x ◇ ((x ◇ y) ◇ y))` |
| Status | Order 10 settled (no model). Orders 2, 3, 6, 7, 8 were already ruled out and models exist at 1, 4, 5, 9, 11, and all large enough orders; 10 was the smallest undecided order in the spectrum catalogue we checked. |
| Main theorem | `E670.no_model_of_order_ten` in [E670/Main.lean](E670/Main.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; kernel-checked reduction + 1,044 LRAT certificates replayed via `native_decide`) |
| Prior art | Checked 23 November 2026: no earlier order-10 exclusion was found (bounded search, not a claim of absolute priority). |

## Theorem

`E670.no_model_of_order_ten` proves that no binary operation on 10 elements satisfies

$$
y \star \bigl(x \star ((x \star y) \star y)\bigr) = x
$$

for all $x, y$.

The proof is computer-assisted and splits cleanly into two verified halves:

1. **Kernel-checked reduction:** Lean's kernel proves that any 10-element model can be renamed so its multiplication table satisfies a fixed Boolean formula in conjunctive normal form (CNF).
2. **Checked SAT/LRAT refutation:** Lean runs a SAT solver on 1,043 subcases plus 1 covering check and replays all 1,044 step-by-step LRAT unsatisfiability certificates with a verified proof checker, proving that the CNF formula has no solution.

## Proof overview

**Proof strategy.** Searching $10^{100}$ multiplication tables blindly is hopeless, and even a single SAT proof for order 10 would be too large to replay. Four steps make the proof both fast and airtight: (1) deduce from the law that every row is a permutation, giving extra algebraic clauses; (2) relabel the 10 elements canonically to crush symmetry without losing any counterexample; (3) encode the normalized table into 1,000 Boolean variables; and (4) split the search into 1,043 small cases plus an untrusted-split covering check.

### Step 1: Rows are permutations (left cancellation)

Fix any row index $y$. As $x$ ranges over all 10 elements, the law $x = y \star \bigl(x \star ((x \star y) \star y)\bigr)$ writes every element $x$ as an entry in row $y$. Since a surjective map from a 10-element set to itself must be injective, **every row is a permutation** — every value appears once per row, and **left cancellation** holds ($y \star u = y \star v \implies u = v$).

Set $a = x \star y$, $b = a \star y$, and $c = x \star b$, so the law states $y \star c = x$. Because left cancellation holds in every row, the same four equalities work in two extra directions that significantly strengthen SAT unit propagation:

* **Cancel row $y$:** if $x \star y = a$, $a \star y = b$, and $y \star c = x$, then $y \star (x \star b) = x = y \star c$, so $x \star b = c$.
* **Cancel rows $y$ and $x$:** if $x \star y = a$, $x \star b = c$, and $y \star c = x$, then $y \star (x \star (a \star y)) = x = y \star c$, so $x \star (a \star y) = c = x \star b$, and hence $a \star y = b$.

### Step 2: Canonical naming (symmetry breaking)

Renaming the 10 elements $\{0, 1, \ldots, 9\}$ (applying a permutation simultaneously to rows, columns, and entries) preserves the law. Therefore, if *any* model exists, a canonically named model exists as well:

1. **Choose $0$:** if some element is non-idempotent ($a \star a \ne a$), name it $0$. Otherwise every element satisfies $x \star x = x$, and any element can be named $0$.
2. **Normalize row $0$:** scan columns $k = 0, 1, 2, \ldots$ from left to right. Whenever $0 \star k > k + 1$, swap the labels $k + 1$ and $0 \star k$. Because both swapped labels are strictly greater than $k$, and every earlier column $y < k$ already satisfies $0 \star y \le y + 1 \le k$, earlier columns and their outputs stay completely untouched.

When the scan ends, row $0$ obeys

$$
0 \star y \le y + 1 \quad \text{for every } y.
$$

This single normalization slashes the number of allowed first rows from $10! = 3,628,800$ down to just $2^9 = 512$ (for each $y \le 8$, only two unused values lie in $\{0, \ldots, y + 1\}$). Lean proves this in `exists_normal` ([E670/Normal.lean](E670/Normal.lean)).

### Step 3: The Boolean formula

Introduce $10^3 = 1,000$ Boolean variables, one for each triple $(x, y, z)$ representing the statement "$x \star y = z$". The CNF clauses assert:

* every cell $(x, y)$ holds a unique value;
* every row contains each value once (permutation rows);
* the law holds in all three directions from Step 1 for all $x, y, a, b, c$;
* $0 \star y \le y + 1$ for every $y$;
* if $0 \star 0 = 0$, then $x \star x = x$ for every $x$ (encoding our choice of $0$).

Lean's kernel proves (`sat_formula` in [E670/Encoding.lean](E670/Encoding.lean)) that every normalized model satisfies all **309,246 clauses**. It remains to show that no truth assignment to the 1,000 variables satisfies them.

### Step 4: Case-split refutation (cube-and-conquer)

A single SAT run would produce a certificate too large to replay, so we partition the search into **1,043 cases** stored in [E670/Cases.lean](E670/Cases.lean). Each case is a short list of equations $x \star y = z$ and disequations $x \star y \ne z$ on the first row and first column, generated by a search script that fixed entries until CaDiCaL refuted each subcase in a few seconds.

**Why the case list does not need to be trusted.** Lean verifies two things (`unsat_of_cubes` in [E670/Cubes.lean](E670/Cubes.lean)):

* **1,043 case certificates:** no assignment satisfies the CNF *and* case $i$.
* **1 covering certificate:** no assignment satisfies the CNF while *avoiding* all 1,043 cases.

Certificates are not stored in the repository. During `lake build`, the `refute` tactic invokes the CaDiCaL binary bundled with Lean and passes its trimmed LRAT proofs as string literals to `Std.Tactic.BVDecide.Reflect.verifyCert`, the formally verified LRAT checker behind `bv_decide`. Because the checker runs via native evaluation (`native_decide`), Lean's compiler and runtime lie inside the trust boundary; the SAT solver, the tactic, and the case list do not.

## Reproduce

Build with the pinned Lean 4.36.0 toolchain and its bundled SAT solver (no other dependencies). From this directory, run:

```sh
lake build
```

The main theorem is `E670.no_model_of_order_ten` in [E670/Main.lean](E670/Main.lean):

```lean
theorem no_model_of_order_ten :
    ¬ ∃ op : Fin 10 → Fin 10 → Fin 10, ∀ x y, op y (op x (op (op x y) y)) = x
```

The build calls CaDiCaL 1,044 times (once per case plus the covering certificate) and checks every certificate in Lean. On an 8-core machine it took 9 minutes with 4.1 GB peak memory, writing about 6.3 GB under `.lake` (mostly certificate text).

Lake builds the 110 case modules in parallel across available cores. On a machine with less RAM, cap Lean's threads:

```sh
LEAN_NUM_THREADS=2 lake build
```

The theorem depends on the standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`) plus 111 native-evaluation axioms (one for each of the 110 case modules and one for the covering certificate), with no admitted lemmas. To check them, run:

```sh
printf '%s\n' 'import E670' '#print axioms E670.no_model_of_order_ten' | lake env lean --stdin
```

### Reading the Lean files

| File | Contents |
| --- | --- |
| [E670/Basic.lean](E670/Basic.lean) | The law, rows as permutations, and the law in three directions. |
| [E670/Normal.lean](E670/Normal.lean) | Element renaming. |
| [E670/Encoding.lean](E670/Encoding.lean) | The CNF formula and the proof that every normalized model satisfies it. |
| [E670/Cubes.lean](E670/Cubes.lean) | Case-split refutation and the `refute` tactic. |
| [E670/Cases.lean](E670/Cases.lean) | The 1,043 cases in 110 groups (data). |
| `E670/Part/`, [E670/Parts.lean](E670/Parts.lean) | One three-line module per group plus their summary. |
| [E670/Main.lean](E670/Main.lean) | The covering certificate and final theorem. |

The renaming, table encoding, case-split machinery, and finite surjection-is-injection lemma do not depend on Equation 670. The [Equation 677 project](../E677-E255-order-9/) imports them from `E670/Basic.lean`, `E670/Normal.lean`, `E670/Encoding.lean`, and `E670/Cubes.lean` for its own 10-element proof.

## Related work

The law is Equation 670 of the [Equational Theories Project](https://teorth.github.io/equational_theories/). Its finite spectrum is tracked in a [spectrum catalogue](https://ohaithe.re/equational_theories/spectrum/?eq=670) on the `definability-negative` branch of [Timeroot/equational_theories](https://github.com/Timeroot/equational_theories), outside the main repository. That Lean development proves exclusions at 2, 3, 6, 7, and 8 and existence at all large enough sizes. Its [order-ten notes](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/docs/order_ten_followup_20261007.md#what-remains-at-ten) record a 10-minute full search plus searches over 97 first rows capped at 100,000 conflicts per row. The [accompanying data](https://github.com/Timeroot/equational_theories/blob/6a653268c6f6173a00e5d7e9d61ad33aca8e52c3/data/spectrum/order_ten_followup_20261007.json) lists 61 rows refuted and 36 undecided.

Our choice of $0$, the bound $0 \star y \le y + 1$, and one variable per statement $x \star y = z$ follow that work. Three details differ: we write clauses directly on table entries without auxiliary variables for $(x \star y) \star y$; we give the solver more time; and we skip sorting the first row's cycles by length (which cuts 512 first rows down to 97, trading 2 to 2.5 times more solver time for a simpler renaming proof).
