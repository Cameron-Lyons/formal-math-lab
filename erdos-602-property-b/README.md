# Erdős Problem #602: Property B for countable sets without singleton intersections

Take a family of **any** size (possibly uncountable) consisting of countably infinite sets, such that any two distinct sets share only finitely many points and never share **exactly one** point. Can we always 2-color the underlying points so that every set in the family contains both colors (that is, does the family have **Property B**, named after Felix Bernstein)?

In a 1987 paper of Erdős, Komjáth asked whether the answer is always yes. This project gives a machine-checked Lean 4 proof answering **yes in full**, working in ZFC with no extra set-theoretic assumptions such as the Continuum Hypothesis.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #602 (`erdosproblems.com/602`), Property B for almost disjoint countable sets with $\lvert A_i \cap A_j \rvert \ne 1$, `FormalConjectures/ErdosProblems/602.lean` |
| Status | Headline statement proved for arbitrary index and ground types in independent universes. |
| Main theorems | `main : type_of% @Erdos602.erdos_602`; general form `E602.exists_colouring` in [Erdos602.lean](Erdos602.lean) |
| Written proof | [Erdos602.md](Erdos602.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos602` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: two limited searches found no earlier proof of the unrestricted statement. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-602-countable-sets-with-no-singleton-intersections). |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | Every family of countably infinite sets with finite pairwise intersections, none of size 1, has Property B. |
| `E602.exists_colouring` (internal) | Same conclusion for countable sets with at least two points each. |

## How the proof works

We build the 2-coloring in countable stages and extend to the entire family by **Zorn's lemma**. Call a set **split** once it contains points of both colors, and call a colored point **settled** once every set through it is split.

To settle a point $y$ of color $c$, we choose a **minimal hitting set** $J$ of uncolored points meeting every unsplit set through $y$ (meaning every $w \in J$ is the sole point of $J$ in some "private" unsplit set $A_{q(w)}$ through $y$) and paint $J$ with the opposite color $c'$. Two mechanisms—**guards** and **0/1 labels**—prevent this process from ever getting stuck or blowing up into an infinite cascade:

* **Guards keep $J$ countable and intersections finite.** Every colored point $z$ carries a *guard*: finitely many split sets whose union contains an uncolored point of every unsplit set through $z$. Drawing $J$ from the sets in $y$'s guard ensures that $J$ is countable and meets each unsplit set through $y$ in a nonempty *finite* set, so a minimal hitting set $J$ always exists.
* **No singleton intersections $\implies$ instant 1-set guards for new points.** After painting $J$ with color $c'$, each $w \in J$ becomes the unique point of color $c'$ in its private newly split set $A_{q(w)}$. Because no two sets meet in a single point, every unsplit set through $w$ shares a second point with $A_{q(w)}$, which can have neither color $c'$ nor color $c$—so it must be uncolored! Thus $\{q(w)\}$ alone guards $w$.
* **0/1 labels keep guard repairs finite.** Each split set carries a label $0$ or $1$: points of color $c$ are guarded only by sets of label $c$, and every set newly split by painting $J$ receives label $c'$. Existing points of color $c$ need no guard repair at all. Meanwhile, because $J$ lives inside finitely many label-$c$ sets and every guard of a color-$c'$ point consists of label-$c'$ sets (hence distinct sets!), finite pairwise intersections guarantee that each old guard loses only *finitely many* points to $J$. Adding the 1-set guards of those finitely many points repairs the guard cleanly!

Repeating this settling step $\omega$ times closes off a countable piece (settling every newly colored point), and Zorn's lemma on closed partial colorings splits every set in the family. For the complete written proof with intuition and Lean correspondence, see [Erdos602.md](Erdos602.md).

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos602
```

**Trust boundary and verification notes:**

* `lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
* `leanchecker` replays the compiled module independently in the Lean kernel.
* The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.
* The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* P. Erdős, [*Some problems on finite and infinite graphs*](https://www.renyi.hu/~p_erdos/1987-28.pdf), Contemp. Math. 65 (1987) 223-228, item 12 (the question is Komjáth's).
* [Erdős Problems #602](https://www.erdosproblems.com/602) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/602.lean#L78)
* Every ingredient is known: minimal hitting sets with private members (Klimó 1993; Ahlswede-Khachatrian; P. L. Erdős 1997; Komjáth 2019) and the local step for finite families (Lovász). The Lean precedent for minimal hitting sets is [grandchallenge/MATHSOLVE #1290](https://github.com/grandchallenge/MATHSOLVE/pull/1290) by fyremael, which was read before this work started. Full credits are in [Erdos602.lean](Erdos602.lean) and [Erdos602.md](Erdos602.md#what-is-new-and-what-is-borrowed).
* To be checked by an expert: the full text of Komjáth, *Set systems with finite chromatic number*, [European J. Combin. 10 (1989) 543-549](https://doi.org/10.1016/S0195-6698(89)80071-X), of which only the abstract was read.
* [Prior-art audit](../PRIOR_ART.md#erdős-602-countable-sets-with-no-singleton-intersections)
