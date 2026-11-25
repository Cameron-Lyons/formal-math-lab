# Erdős Problem #602 (Erdos #602): Property B for countable sets with no singleton intersections — Lean 4 proof

**Status: answered "yes" for the full statement.** Take any family, of any size, of countably infinite sets such that any two of them have finitely many common points, and never exactly one. Komjáth asked, in a paper of Erdős (1987), whether the points can always be colored with two colors so that every set of the family contains both colors. This Lean 4 project proves that they can, in ZFC with no further hypothesis.

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Erdős Problem #602** (`Erdos #602`, `erdosproblems.com/602`), Property B, almost disjoint countable sets, `\|A_i ∩ A_j\| ≠ 1`, `FormalConjectures/ErdosProblems/602.lean` |
| **Status** | **Headline statement proved**, for arbitrary index and ground types in independent universes. |
| **Main Lean theorems** | `main : type_of% @Erdos602.erdos_602`; the general form is `E602.exists_colouring`, in [Erdos602.lean](Erdos602.lean) |
| **Written proof** | [Erdos602.md](Erdos602.md), with the same lemma numbers as the Lean file |
| **Verification** | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos602` (Lean 4.33.1 + Formal Conjectures) |
| **Prior-art status** | Checked **25 November 2026**: no earlier proof of the unrestricted statement located in two limited searches. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-602-countable-sets-with-no-singleton-intersections). |

## What Lean proves

| Lean declaration | Result |
| --- | --- |
| `main` | Every family of countably infinite sets with finite pairwise intersections, none of size 1, has Property B. |
| `E602.exists_colouring` (internal) | The same for countable sets with at least two points each. |

## Idea of the proof

Color countably many points at a time. A set is *split* once it contains both colors. To finish a colored point $y$, give the opposite color to a minimal set $J$ of uncolored points that meets every unsplit set through $y$. Each colored point carries a *guard*: finitely many split sets that contain an uncolored point of every unsplit set through it. The hypothesis "no singleton intersections" gives each new point a guard consisting of a single set, and labels on the split sets ensure that the old guards lose only finitely many points, which can be repaired. Repeating this $\omega$ times, and then Zorn's lemma, reaches every set.

## Reproduce

Run from this directory with the pinned Lean **4.33.1** toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos602
```

`lake build` checks the proof, that the type of `main` comes from the upstream statement (`type_of%`), and that `main` uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the part of Formal Conjectures that the statement imports, which takes a while. Formal Conjectures is a dependency pinned at commit `9097e2f9`; only its statements, definitions and proved lemmas are used, never the theorem it leaves as `sorry`.

The mathematics, the Lean proof and the literature searches are the work of AI agents. **No human has reviewed this project.**

## References and attribution

* P. Erdős, [*Some problems on finite and infinite graphs*](https://www.renyi.hu/~p_erdos/1987-28.pdf), Contemp. Math. 65 (1987) 223–228, item 12; the question is Komjáth's.
* [Erdős Problems #602](https://www.erdosproblems.com/602) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/602.lean#L78)
* Every ingredient is known: minimal hitting sets with private members (Klimó 1993; Ahlswede–Khachatrian; P. L. Erdős 1997; Komjáth 2019) and the local step for finite families (Lovász). The Lean precedent for minimal hitting sets is [grandchallenge/MATHSOLVE #1290](https://github.com/grandchallenge/MATHSOLVE/pull/1290) by fyremael, which was read before this work started. Full credits are in [Erdos602.lean](Erdos602.lean) and [Erdos602.md](Erdos602.md#what-is-new-and-what-is-borrowed).
* To be checked by an expert: the full text of Komjáth, *Set systems with finite chromatic number*, [European J. Combin. 10 (1989) 543–549](https://doi.org/10.1016/S0195-6698(89)80071-X), of which only the abstract was read.
* [Dated prior-art audit](../PRIOR_ART.md#erdős-602-countable-sets-with-no-singleton-intersections)
