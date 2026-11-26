# Erdős Problem #338: restricted order bounded by the order

A set $A$ of non-negative integers is a basis of order $h$ if every large integer is a sum of at most $h$ elements of $A$, repetition allowed. Its restricted order is the least $t$, if one exists, such that every large integer is a sum of at most $t$ distinct elements of $A$. Erdős and Graham (1980, question 3(ii)) asked whether the restricted order, when it exists, is bounded in terms of $h$ alone. Our Lean 4 proof shows that it is. We do not address the headline question.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #338, bounded-by-order variant (`erdosproblems.com/338`), Erdős and Graham 1980 question 3(ii), `erdos_338.variants.bounded_by_order` in `FormalConjectures/ErdosProblems/338.lean` |
| Status | Variant proved, with an explicit but very large bound $f(h)$. Questions 3(i) (which bases have a restricted order) and 3(iii) (when the two orders agree) are not addressed. |
| Main theorem | `main : type_of% @Erdos338.erdos_338.variants.bounded_by_order` in [Erdos338.lean](Erdos338.lean) |
| Written proof | [Erdos338.md](Erdos338.md), with the same lemma numbers as the Lean file |
| Verification | `lake exe cache get && lake build && LEAN_NUM_THREADS=1 lake env leanchecker Erdos338` (Lean 4.33.1 + Formal Conjectures) |
| Prior art | Checked 25 November 2026: two limited searches found no earlier bound depending only on $h$. The proof follows the strategy of Chen, Yang, and Zhao (18 November 2026), whose arguments appear to imply such a bound. See [PRIOR_ART.md](../PRIOR_ART.md#erdős-338-restricted-order-bounded-by-the-order). |

## Idea of the proof

Call a number *robust* if it can still be written as a sum of at most $k$ distinct elements of $A$ even after any $q$ elements are forbidden. Robust numbers can be added with repetition, because each copy can use fresh elements. Counting shows that at every large scale $N$, at least a $1/c$ fraction of the numbers up to $2N$ are robust, where $c$ belongs to a finite set of constants depending only on $h$.

A pigeonhole argument then represents all multiples of a modulus $g(c)$ in a long interval as sums of boundedly many robust numbers. To represent a target integer, we first fix its residue modulo $g(c)$ using fewer than $g(c)$ distinct elements of $A$. Since $q$ is chosen after $g(c)$, the robust summands avoid those elements. Comparing consecutive scales bridges the gaps between intervals.

## Reproduce

Run from this directory with the pinned Lean 4.33.1 toolchain:

```sh
lake exe cache get
lake build
LEAN_NUM_THREADS=1 lake env leanchecker Erdos338
```

`lake build` checks the proof, confirms that `main` matches the upstream statement type (via `type_of%`), and verifies that `main` uses only `propext`, `Classical.choice`, and `Quot.sound`. `leanchecker` replays the module in the Lean kernel. The first build also compiles the imported part of Formal Conjectures (pinned at commit `9097e2f9`). We use only its statements, definitions, and proved lemmas, never any theorem left as `sorry`.

The mathematics, Lean proof, and literature searches were produced by AI agents. No human has reviewed this project.

## References and attribution

* P. Erdős and R. L. Graham, [*On bases with an exact order*](https://static.renyi.hu/~p_erdos/1980-22.pdf), Acta Arith. 37 (1980) 201-207, remark 3(ii).
* [Erdős Problems #338](https://www.erdosproblems.com/338) and [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/ErdosProblems/338.lean#L97)
* S.-Q. Chen, Q.-H. Yang, and L. Zhao, [*On a problem of Erdős and Graham related to restricted order*](https://github.com/csq20180327/Erdos338) (18 November 2026, unrefereed), characterize which bases have a restricted order; we follow their strategy. They do not state a bound depending only on $h$, though a uniform bound appears within reach of their method.
* Earlier instances of this strategy appear in D. Veljjanoski, [erdos338](https://github.com/veljjanoski/erdos338) (1 October 2026). N. Hegyvári, F. Hennecart, and A. Plagne (2007) also ask for the bound and prove lower bounds. Full credits are in [Erdos338.lean](Erdos338.lean) and [Erdos338.md](Erdos338.md#what-is-new-and-what-is-borrowed).
* [Prior-art audit](../PRIOR_ART.md#erdős-338-restricted-order-bounded-by-the-order)
