# Arithmetic-progression intersections on thirteen points

The maximum is **82**. The members are distinct subsets of $\{1,\ldots,13\}$, and the intersection of every two different members must be a nonempty arithmetic progression. Singletons and pairs count as progressions. This settles the thirteen-point case of Erdős problem #272. [One-page proof (PDF)](proof.pdf) · [Typst source](proof.typ) · [Problem statement](https://www.erdosproblems.com/272)

## Why 82 is attainable

Start with the 79 sets of size at most three that contain 7. For each $d=1,2,3$, remove the triples $\{7-2d,7,7+d\}$ and $\{7-d,7,7+2d\}$. Add the five-term progression with centre 7 and step $d$, and both of its four-term subprogressions. This gives $79-6+9=82$ sets. The Lean theorem `Erdos272.exists_family_82` checks distinctness and all 3,321 pairwise intersections in Szabó's construction using only Lean's built-in `Init` prelude. [Lean proof](Erdos272.lean)

## Why 83 is impossible

For families with a common element, Yang's starred-family theorem gives the upper bound 82. The C++ verifier checks this directly. For each point it greedily partitions the sets containing that point into at most 82 classes, placing two sets in the same class only when their intersection is not a progression. A family takes at most one set from each class. [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004)

For families with no common element, set aside the 300 subsets containing a seven-term progression. Record a constant 1 and the indicators of the 78 pairs for each remaining member. The squared-norm identity and an explicit analysis of the 15 five-term progression relations in the one-page proof show that these vectors are linearly independent, so at most 79 remaining members can occur. [Dimension bound](proof.pdf)

A counterexample of size 83 therefore needs at least four of the 300 distinguished sets. Ordering them in reflection pairs under $i\mapsto 14-i$ leaves 3,224 canonical compatible choices for the first two. The C++ verifier checks the 7,891-mask score bound, the direct starred bound at 13, and every one of the 3,224 initial pairs for an 83-clique with empty total intersection. None exists. The written argument and exhaustive C++ computation establish the upper bound; the Lean theorem establishes the lower bound. [C++ verifier](clique_search/verify.cpp) · [Dated prior-art notes](../PRIOR_ART.md#erdős-272-arithmetic-progression-intersections-on-thirteen-points)

## Reproduce

Run from this directory with Lean 4.36.0 and a C++23 compiler.

```sh
lake --wfail build
lake env leanchecker --fresh Erdos272
c++ -O3 -std=c++23 -march=native clique_search/verify.cpp -o /tmp/erdos272-verify
/tmp/erdos272-verify
```
