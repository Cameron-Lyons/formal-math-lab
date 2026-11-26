# Arithmetic-progression intersections on thirteen points

The maximum is **82**. The members are distinct subsets of $\{1,\ldots,13\}$, and the intersection of every two different members must be a nonempty arithmetic progression. Singletons and pairs count as progressions. This settles the thirteen-point case of Erdős problem #272. [One-page proof (PDF)](proof.pdf) · [Typst source](proof.typ) · [Problem statement](https://www.erdosproblems.com/272)

## Why 82 is attainable

Start with the 79 sets of size at most three that contain 7. For each $d=1,2,3$, remove the triples $\{7-2d,7,7+d\}$ and $\{7-d,7,7+2d\}$. Add the five-term progression with centre 7 and step $d$, and both of its four-term subprogressions. This gives $79-6+9=82$ sets. The Lean theorem `Erdos272.exists_family_82` checks distinctness and all 3,321 pairwise intersections in Szabó's construction. [Lean proof](Erdos272.lean)

## Why 83 is impossible

Yang's starred-family theorem covers families with a common element. For the other families, set aside the 300 subsets containing a seven-term progression and the 15 five-term progressions. For every remaining member record a constant 1 and the indicators of its 78 pairs. The squared-norm identity in the one-page proof shows that these vectors are linearly independent, so at most 79 remaining members can occur. [Yang, Theorem 1.4](https://arxiv.org/abs/2607.23004) · [Dimension bound](proof.pdf)

A counterexample would therefore use at least four of the 315 distinguished sets. In a fixed order there are 9,862 compatible choices for its first two. The C++ verifier checks whether their common neighbors can supply 81 more sets, including two further distinguished sets, with empty total intersection. None can. The written argument and the exhaustive computation establish the upper bound. The Lean theorem establishes the lower bound. [C++ verifier](clique_search/verify.cpp) · [Dated prior-art notes](../PRIOR_ART.md#erdős-272-arithmetic-progression-intersections-on-thirteen-points)

## Reproduce

Run from this directory with Lean 4.36.0 and a C++20 compiler.

```sh
lake build
lake env leanchecker --fresh Erdos272
c++ -O3 -std=c++20 -march=native clique_search/verify.cpp -o /tmp/erdos272-verify
/tmp/erdos272-verify --simple
```

The `--simple` run checks that the score vanishes on progressions and is positive on all other sets among the 7,891 nonempty subsets containing no seven-term progression. It then searches the 315-set case split. Bit zero represents 1 in both implementations.

A faster replay keeps the five-term progressions in the dimension argument. The two-element members either lie in a triangle or share a point. In the latter case some member of the full family misses that point. For each triangle and each possible choice of that member and point, Python checks that the eligible progression rows are independent modulo two and hence over the reals. The corresponding C++ search uses 300 distinguished sets and 6,357 compatible initial pairs. The script also verifies the starred bound directly at 13 and rechecks the construction. Run both commands for this version. [Finite arithmetic and rank checks](short_bound.py)

```sh
python3 short_bound.py
/tmp/erdos272-verify
```
