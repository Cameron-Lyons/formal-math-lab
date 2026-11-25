# Equation 17260 (E17260 / dual E28740): partial finite-model obstructions — Lean 4 proofs

**Status: the finite-model existence question remains open.** This Lean 4 project proves structural and counting obstructions that any nontrivial finite magma satisfying **Equation 17260** (`E17260`, dual **Equation 28740** / `E28740`) of the [Equational Theories Project](https://teorth.github.io/equational_theories/) must obey:

$$
x = (y \star x) \star \bigl(z \star (x \star (z \star z))\bigr)
$$

for all $x, y, z$. In plain-text / ETP notation, the law is `x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))` (or `x = (y * x) * (z * (x * (z * z)))`).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | Equational Theories Project **Equation 17260** (`E17260`, `Equation17260`; dual **Equation 28740**, `E28740`), existence of a nontrivial finite magma |
| **Law** | `x = (y ◇ x) ◇ (z ◇ (x ◇ (z ◇ z)))` (`x = (y * x) * (z * (x * (z * z)))`) |
| **Status** | **Partial results only; finite nontrivial existence remains open.** Infinite models are already known (prior work, arXiv:2609.05690). |
| **Main Lean theorems** | `Equation17260.subsingleton_of_surjective_square`, `subsingleton_of_one_idempotent`, `subsingleton_of_square_two_cycle`, `subsingleton_of_left_cancel`, `subsingleton_of_right_cancel`, `affine_subsingleton` |
| **Verification** | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib v4.36.0; pure kernel proofs, no `sorry`, no `native_decide`) |
| **Prior-art status** | Checked **23 November 2026**: infinite models and exclusions through order 10 and finite linear models are prior work; novelty of the other partial obstructions is unverified. See [PRIOR_ART.md](../PRIOR_ART.md#e17260-partial-results-finite-existence-unresolved). |

## Proved obstructions

A magma satisfying Equation 17260 has at most one element (`Subsingleton`) if **any one** of the following holds:

* There is an idempotent element $e$ with $e \star e = e$.
* Squaring is surjective: every element equals $x \star x$ for some $x$ (no finiteness assumption needed).
* The squaring map has a 2-cycle: $a \star a = b$ and $b \star b = a$.
* The operation satisfies left cancellation or right cancellation.
* The operation is affine: $x \star y = A(x) + B(y) + c$, where $A, B$ are additive endomorphisms of a commutative additive monoid (no finiteness assumption needed).

Consequently, in any nontrivial finite model, the squaring map $x \mapsto x \star x$ must miss at least one element, map two distinct elements to the same square, and have no cycles of length 1 or 2. **These restrictions do not yet give a contradiction.**

As an illustration, the right-cancellation proof takes two cancellations: fix $x, z$ and write $t = z \star (x \star (z \star z))$. The law gives $(y \star x) \star t = (x \star x) \star t$ for every $y$. Cancelling $t$ gives $y \star x = x \star x$, and cancelling $x$ gives $y = x$.

## Main theorem endpoints

All declarations below are in the `Equation17260` namespace and assume `Law op` (`Subsingleton` means at most one element):

| Declaration | File | Additional assumption and conclusion |
| --- | --- | --- |
| `subsingleton_of_surjective_square` | [Squares17260.lean](Squares17260.lean) | Every element is `op x x` for some `x` $\implies$ `Subsingleton` (no finiteness assumption). |
| `subsingleton_of_one_idempotent` | [Cancellation17260.lean](Cancellation17260.lean) | Some `e` satisfies `op e e = e` $\implies$ `Subsingleton`. |
| `subsingleton_of_square_two_cycle` | [Cancellation17260.lean](Cancellation17260.lean) | `op a a = b` and `op b b = a` $\implies$ `Subsingleton`. |
| `subsingleton_of_left_cancel`, `subsingleton_of_right_cancel` | [Cancellation17260.lean](Cancellation17260.lean) | Left or right cancellation $\implies$ `Subsingleton`. |
| `affine_subsingleton` | [Affine17260.lean](Affine17260.lean) | `op x y = A x + B y + c` for additive endomorphisms of a commutative additive monoid $\implies$ `Subsingleton`. |
| `exists_square_collision`, `exists_not_square` | [Squares17260.lean](Squares17260.lean) | Every finite nontrivial model has a square collision and a missing square (`exists_not_square` holds without finiteness). |
| `sum_column_card_le`, `card_le_row_card_sq` | [Finite17260.lean](Finite17260.lean) | Finite column-image and row-image cardinality bounds. |

Start with [Cancellation17260.lean](Cancellation17260.lean) and [Squares17260.lean](Squares17260.lean). [Affine17260.lean](Affine17260.lean) excludes affine constructions and [Finite17260.lean](Finite17260.lean) proves the counting bounds. [TheoryNotes.txt](TheoryNotes.txt) gives longer mathematical arguments, and [ModelNotes.txt](ModelNotes.txt) documents our search scripts and their limitations (searches at sizes 11–20 were inconclusive and do not improve the known order-10 exclusion).

## Check the proofs

With the pinned Lean 4.36.0 and mathlib dependencies available, run from this directory:

```sh
lake exe cache get
lake build
lake env lean Check.lean
```

`lake exe cache get` downloads the pinned mathlib build cache on a fresh checkout (`lake-manifest.json` records exact dependency commits). [Check.lean](Check.lean) audits all main results; there are no `sorry` proofs, custom axioms, or `native_decide` checks.

## Prior work

Checked **23 November 2026**:

* [*Trace-Tree Magmas* (arXiv:2609.05690v3, Table 4 & §9)](https://arxiv.org/html/2609.05690v3#S7.SS2) provides Lean-certified **infinite** models of E17260 while explicitly leaving finite-model existence open.
* The [December 2024 Equational Theories Zulip discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html) already reports exhaustive exclusion of orders 2–10 and absence of finite linear models (including noncommutative coefficients).

The novelty of the remaining partial obstructions here has not been established. See the collection's [dated prior-art audit](../PRIOR_ART.md#e17260-partial-results-finite-existence-unresolved) for exact source references and scope.
