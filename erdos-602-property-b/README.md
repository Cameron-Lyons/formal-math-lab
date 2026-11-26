# Erdős Problem #602: Property B for countable sets without singleton intersections

Take a family of any size consisting of countably infinite sets, where any two sets share finitely many points and never exactly one. In a 1987 paper of Erdős, Komjáth asked whether the points can always be 2-colored so that every set in the family contains both colors. Our Lean 4 proof answers yes in full, working in ZFC with no extra assumptions.

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

## Idea of the proof

We color countably many points at a time, calling a set *split* once it contains both colors. To settle a colored point $y$, we assign the opposite color to a minimal set $J$ of uncolored points that meets every unsplit set through $y$.

Each colored point carries a *guard*: finitely many split sets that contain an uncolored point of every unsplit set through it. Because no two sets meet in a single point, every newly colored point gets a guard consisting of a single set. Labels on the split sets ensure that old guards lose only finitely many points, so they can be repaired. Repeating this $\omega$ times closes off a countable piece, and Zorn's lemma extends the coloring to every set.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos602
```

`lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.

The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* P. Erdős, [*Some problems on finite and infinite graphs*](https://www.renyi.hu/~p_erdos/1987-28.pdf), Contemp. Math. 65 (1987) 223-228, item 12 (the question is Komjáth's).
* [Erdős Problems #602](https://www.erdosproblems.com/602) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/602.lean#L78)
* Every ingredient is known: minimal hitting sets with private members (Klimó 1993; Ahlswede-Khachatrian; P. L. Erdős 1997; Komjáth 2019) and the local step for finite families (Lovász). The Lean precedent for minimal hitting sets is [grandchallenge/MATHSOLVE #1290](https://github.com/grandchallenge/MATHSOLVE/pull/1290) by fyremael, which was read before this work started. Full credits are in [Erdos602.lean](Erdos602.lean) and [Erdos602.md](Erdos602.md#what-is-new-and-what-is-borrowed).
* To be checked by an expert: the full text of Komjáth, *Set systems with finite chromatic number*, [European J. Combin. 10 (1989) 543-549](https://doi.org/10.1016/S0195-6698(89)80071-X), of which only the abstract was read.
* [Prior-art audit](../PRIOR_ART.md#erdős-602-countable-sets-with-no-singleton-intersections)
