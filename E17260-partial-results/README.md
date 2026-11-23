# Equation 17260: partial results

**We have not solved the finite-model question.** The Lean proofs establish
necessary conditions for a possible solution.

The required law is
\[
x=(y*x)*(z*(x*(z*z)))\quad\text{for all }x,y,z.
\]

A model has at most one element if **any one** of these conditions holds:

- There is an element `e` with `e*e = e`.
- Every element is a square `x*x`.
- The operation permits left cancellation or right cancellation.
- The operation is affine: `x*y = A(x) + B(y) + c`, using additive
  endomorphisms of a commutative additive monoid.

Also, `a*a = b` and `b*b = a` force the model to be trivial. Consequently,
any nontrivial finite model must have a square map that misses an element,
maps two distinct elements to the same square, and has no cycles of length
one or two. **These restrictions do not yet give a contradiction.**

For example, the right-cancellation proof takes two cancellations. Fix `x,z`
and write `t = z*(x*(z*z))`. The law gives `(y*x)*t = (x*x)*t` for every `y`.
Cancel `t` to obtain `y*x = x*x`, then cancel `x` to obtain `y = x`.

## Check the proofs

With the pinned Lean 4.36.0 and mathlib dependencies available, run:

```sh
lake build
```

For a fresh checkout, first run `lake exe cache get` to obtain the pinned
dependencies and their build cache. `lake-manifest.json` records the dependency commits.
`Check.lean` audits all main results; there are no `sorry` proofs or custom axioms.

## Main theorem endpoints

All declarations below are in the `Equation17260` namespace and assume `Law op`.
`Subsingleton` means at most one element.

| Declaration | Additional assumption and conclusion |
| --- | --- |
| `subsingleton_of_surjective_square` | Every element is `op x x` for some `x` ⇒ `Subsingleton`. No finiteness assumption. |
| `subsingleton_of_one_idempotent` | Some `e` satisfies `op e e = e` ⇒ `Subsingleton`. |
| `subsingleton_of_square_two_cycle` | `op a a = b` and `op b b = a` ⇒ `Subsingleton`. |
| `subsingleton_of_left_cancel`, `subsingleton_of_right_cancel` | The respective cancellation law ⇒ `Subsingleton`. |
| `affine_subsingleton` | `op x y = A x + B y + c` for additive endomorphisms of a commutative additive monoid ⇒ `Subsingleton`. |
| `exists_square_collision`, `exists_not_square` | Every finite nontrivial model has a square collision and a missing square. The missing-square result also holds without finiteness. |
| `sum_column_card_le`, `card_le_row_card_sq` | Finite column-image and row-image cardinality bounds. |

Start with `Cancellation17260.lean` and `Squares17260.lean`.
`Affine17260.lean` excludes affine constructions; `Finite17260.lean` proves
counting bounds. `TheoryNotes.txt` gives the longer mathematical arguments.
Search scripts and their limitations are documented in `ModelNotes.txt`.
Our searches at sizes 11–20 were inconclusive.

## Prior work

Checked **23 November 2026**. The
[September 2026 paper, Table 4](https://arxiv.org/html/2609.05690v3#S7.SS2)
provides Lean-certified infinite models of E17260 while explicitly leaving
finite-model existence open. The
[December 2024 discussion](https://leanprover-community.github.io/archive/stream/458659-Equational/topic/Some.20results.20from.20order.205.html)
already excludes models of sizes 2–10 and finite linear models.
The novelty of our other partial results has not been established.
See the collection's [dated prior-art audit](../PRIOR_ART.md#e17260-partial-results-finite-existence-unresolved)
for exact source references and the scope of this claim.
