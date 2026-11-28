# Arithmetic-progression intersections on thirteen points

**Erdős Problem #272** asks how many distinct subsets of $\{1, \ldots, n\}$ you can collect so that the intersection of *every two different subsets* is a nonempty **arithmetic progression** (numbers spaced by a constant step, with singletons and pairs automatically counting as progressions).

For $n = 13$, this directory proves that the exact maximum is **82**:

* **Lower bound ($\ge 82$) — Lean 4:** `Erdos272.exists_family_82` in [Erdos272.lean](Erdos272.lean) verifies Szabó's 82-set construction (distinctness and all $\binom{82}{2} = 3,321$ pairwise intersections) using only Lean's built-in `Init` prelude.
* **Upper bound ($\le 82$) — Written proof + exhaustive C++23 computation:** the [one-page proof (Typst source)](proof.typ) establishes a linear-algebraic dimension bound, and the standalone [C++ verifier](clique_search/verify.cpp) exhaustively rules out every candidate 83-set family.

## At a glance

| Field | Summary |
| --- | --- |
| Problem | [Erdős Problem #272](https://www.erdosproblems.com/272) at $n = 13$ |
| Theorem | Maximum family size on $\{1, \ldots, 13\}$ is **82** |
| Lower bound (Lean 4) | `Erdos272.exists_family_82` in [Erdos272.lean](Erdos272.lean) (`Init` prelude only) |
| Upper bound (Proof + C++) | [One-page proof (Typst)](proof.typ) + [C++ verifier](clique_search/verify.cpp) |

## Why 82 is attainable

Szabó's construction builds an 82-set family centered at the midpoint $7$:

1. Start with all subsets of $\{1, \ldots, 13\}$ of size at most 3 containing $7$: there are $1 + 12 + \binom{12}{2} = 79$ such sets. Any two distinct sets of size $\le 3$ meet in at most 2 elements (and share $7$), so every pairwise intersection is a singleton or pair—automatically an arithmetic progression.
2. For each step $d = 1, 2, 3$, perform a net $+1$ swap around $7$:
   * **Remove** the 2 non-progression triples $\{7 - 2d, 7, 7 + d\}$ and $\{7 - d, 7, 7 + 2d\}$.
   * **Add** the 3 progressions: the 5-term progression centered at $7$ with step $d$, together with both of its 4-term subprogressions.

This yields $79 - 6 + 9 = 82$ sets. The Lean theorem `Erdos272.exists_family_82` checks distinctness and all 3,321 pairwise intersections using only Lean's built-in `Init` prelude ([Lean proof](Erdos272.lean)).

## Why 83 is impossible

Any hypothetical family of size 83 either shares a common point across all members or has empty total intersection. We rule out both cases:

### Case 1: Families with a common element (starred families)

[Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) gives the upper bound 82 for starred families. The [C++ verifier](clique_search/verify.cpp) also checks this directly at $n = 13$: for each point $x \in \{1, \ldots, 13\}$, it greedily partitions all subsets containing $x$ into at most 82 incompatible classes, placing two sets in the same class only when their intersection is *not* a progression. Because a valid family takes at most one set from each class, no starred family can exceed size 82.

### Case 2: Families with no common element

1. **Linear-algebraic dimension bound:** Set aside the **300** subsets of $\{1, \ldots, 13\}$ that contain a 7-term arithmetic progression. For each remaining member of the family, record a 79-entry vector consisting of a constant $1$ plus the indicator bits of all $\binom{13}{2} = 78$ pairs of points. A squared-norm identity and an explicit analysis of the 15 five-term progression relations in the [one-page proof](proof.typ) prove that these vectors are linearly independent—so at most **79** non-distinguished members can appear.
2. **Reduction to 3,224 canonical starting pairs:** Any 83-set counterexample must therefore contain at least $83 - 79 = 4$ of the 300 distinguished sets. Ordering those 300 sets in reflection pairs under $i \mapsto 14 - i$ leaves **3,224** canonical compatible choices for the first two distinguished sets.
3. **Exhaustive C++ check:** The [C++ verifier](clique_search/verify.cpp) checks the 7,891-mask score bound, the direct starred bound at 13, and every one of the 3,224 initial pairs for an 83-clique with empty total intersection. None exists.

**Trust boundary:** The written argument and exhaustive C++ computation establish the upper bound ($\le 82$); the Lean theorem establishes the lower bound ($\ge 82$).

## Reproduce

Run from this directory with Lean 4.36.0 and a C++23 compiler:

```sh
lake --wfail build
lake env leanchecker --fresh Erdos272
c++ -O3 -std=c++23 -march=native clique_search/verify.cpp -o /tmp/erdos272-verify
/tmp/erdos272-verify
```
