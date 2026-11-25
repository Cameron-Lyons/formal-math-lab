# Erdős Problem #677: equal LCMs of consecutive integers

Write $M(n, k) = \operatorname{lcm}(n + 1, n + 2, \ldots, n + k)$ for the least common multiple of $k$ consecutive positive integers. Erdős Problem #677 asks whether $M(m, k) \ne M(n, k)$ whenever $k > 0$ and $m \ge n + k$ (disjoint equal-length blocks). The general question over all $k$ remains open.

The Lean 4 proofs here classify lengths $k = 2, 3, 4$ inside Lean (no external computation), give a computer-assisted classification for $k = 6$ (Lean reduction plus external elliptic-curve arithmetic), and prove shift, endpoint, and height exclusions. Definitions match `FormalConjectures/ErdosProblems/677.lean`.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #677 (`erdosproblems.com/677`), equal LCMs of consecutive integers $M(m, k) = M(n, k)$, `FormalConjectures/ErdosProblems/677.lean` |
| Status | Lengths $k = 2, 3, 4$ proved in Lean 4; length $k = 6$ settled computer-assisted (Lean checks the reduction and finite cases; external elliptic-curve arithmetic proves the affine bound). General $k$ remains open. |
| Classifications | For distinct starts $m > n$: $k = 2$, none; $k = 3$, only $(n, m) = (2, 3)$ ($\operatorname{lcm} = 60$, overlapping); $k = 4$, only $(1, 2)$ ($\operatorname{lcm} = 60$, overlapping); $k = 6$, only $(3, 4)$, $(5, 6)$, $(13, 15)$ (all overlapping). |
| Main theorems | `Erdos677.erdos_677_two`, `erdos_677_three`, `erdos_677_four`, `three_collision_iff`, `four_collision_iff`, `six_collision_iff_three_of_affine_cover`, `no_collision_shift_le_52` |
| Verification | `lake exe cache get && lake build` (Lean 4.35.0-rc2 + mathlib); see [cubic/LengthSix.md](cubic/LengthSix.md#reproduction) for length-6 elliptic-curve arithmetic |
| Prior art | Checked 23-24 November 2026: classifications at $k = 3, 4$, the three overlapping pairs at $k = 6$, and the four-cubic reduction were recorded previously; no earlier Lean proof of $k = 3$ or $k = 4$ or complete $k = 6$ integral-point proof was located (priority unverified). See [PRIOR_ART.md](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers). |

## Results

* Length $k = 2$: $M(n, 2) = (n+1)(n+2)$ strictly increases with $n$, so no collisions occur (`Erdos677.erdos_677_two`).
* Lengths $k = 3$ and $k = 4$ (pure Lean 4): for distinct starts, the only equalities are $M(2, 3) = M(3, 3) = 60$ and $M(1, 4) = M(2, 4) = 60$. Both pairs overlap, so no disjoint blocks have equal LCM ([LengthThreeAndFour.md](LengthThreeAndFour.md)).
* Length $k = 5$: Lean rules out disjoint collisions for 87 of the 144 ordered residue pairs modulo 12 and for all reduced slopes of height at most $3 \cdot 10^{12}$ ([LengthTwoAndFive.md](LengthTwoAndFive.md)).
* Length $k = 6$ (computer-assisted): for arbitrary distinct starts, the only equalities are the three overlapping pairs $(n, m) \in \{(3, 4), (5, 6), (13, 15)\}$. Lean verifies the reduction to four plane cubics, the finite LCM checks, and the disjoint-block conclusion given the affine bound; external arithmetic using elliptic logarithms and David's theorem proves the bound and enumerates all integral points ([cubic/LengthSix.md](cubic/LengthSix.md)).
* General families in Lean: Lean proves $M(m, k) \ne M(n, k)$ for adjacent disjoint blocks ($m = n + k$) of all lengths $k$, for every earlier block starting at $n = 0$ (integers $1, \ldots, k$), and for every positive shift $m - n$ divisible by all integers $1, \ldots, k - 1$.

### Verified finite and shift ranges

| Range | Verification |
| --- | --- |
| All lengths, later endpoint $m + k \le 1000$ | Lean kernel, `no_collision_through_1000` |
| All lengths, start difference $m - n \le 52$, arbitrary starts | Lean kernel, `no_collision_shift_le_52` |
| Lengths 5 and 6, earlier parameter $n \le 10^{20}$, arbitrary later start | Lean kernel, `no_collision_five_six` |
| All lengths, later endpoint $m + k \le 10{,}000{,}000$ | Exhaustive C++ search |
| All lengths, start difference $m - n \le 7000$, arbitrary starts | Lean kernel reduction to the C++ search |
| Lengths 5 and 6, earlier parameter $n \le 10^{1000}$, arbitrary later start | Exact Python search |
| Lengths 7 through 24, earlier parameter $n \le 10^{100}$, arbitrary later start | Exact Python search |
| Lengths 25 through 28, earlier parameter $n \le 10^{20}$, arbitrary later start | Exact Python search |

## Lean declarations

* `Erdos677.three_collision_iff` and `Erdos677.four_collision_iff` classify all equal LCMs at lengths $k = 3$ and $k = 4$.
* `Erdos677.erdos_677_two`, `Erdos677.erdos_677_three`, and `Erdos677.erdos_677_four` prove the disjoint-block inequality at lengths $k = 2, 3, 4$.
* `Erdos677.six_collision_on_cubics` sends a repeated length-6 LCM to an integral point on one of four plane cubics.
* `Erdos677.six_collision_iff_three_of_affine_cover` derives the three-pair classification at length 6 from the complete integral-point list.
* `Erdos677.no_collision_six_of_affine_bound` excludes disjoint length-6 blocks from the analytic affine bound alone.

For length 6, the Lean files state both hypotheses explicitly, and the external scripts check the global bound and enumerate the integral points ([SixCubics.lean](SixCubics.lean), [reproduction notes](cubic/LengthSix.md#reproduction)).

## Proof methods and verification

Run from this directory with `elan` installed (pinned Lean 4.35.0-rc2):

```sh
lake exe cache get
lake build
c++ -O3 -std=c++17 search/search.cpp -o /tmp/erdos677-search
/tmp/erdos677-search 10000000
python search/displacement.py
python search/height.py --exponent 1000 5 6
python search/height.py --tight-bound --exponent 100 7 8 9 10 11 12 13 14 15 16
python search/height.py --coefficient-sieve --exponent 100 17 18 19 20 21 22 23 24
python search/height.py --coefficient-sieve --exponent 20 25 26 27 28
python -m unittest discover -s search
```

* Prime-power filter ([PrimePowers.lean](PrimePowers.lean)): a prime power divides a block LCM iff it divides an entry. If the later block contains a prime power itself, that power exceeds every earlier entry, so the C++ search discards it; for remaining blocks it hashes prime powers above $k$ and compares exact matches.
* Displacement bounds ([BinomialBounds.lean](BinomialBounds.lean), [Displacement.lean](Displacement.lean)): every prime power of a common LCM divides a positive difference between entries, which for start difference $d = m - n$ lies in $[d - k + 1, d + k - 1]$. Upper and lower binomial bounds on these intervals give an inequality checked in Lean through $d \le 7000$.
* Slope and height bands ([FixedLength.lean](FixedLength.lean), [Height.lean](Height.lean), [search/height.py](search/height.py)): each block LCM has the form $t k \binom{n+k}{k}$ with $t \mid M(0, k)/k$. For lengths 5 and 6 this leaves seven and four possible product ratios, confining the doubled block centers to narrow bands around lines of algebraic slope checked in Lean and extended in exact Python arithmetic.

## References and attribution

* [Erdős Problems #677](https://www.erdosproblems.com/677) and [Erdős Problem a Day #677](https://erdosproblemaday.com/problem/677)
* [Formal Conjectures `ErdosProblems/677.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean)
* [UpstreamInterval.lean](UpstreamInterval.lean) reproduces the Formal Conjectures definition of `Finset.lcmInterval` under its [Apache-2.0 license](LICENSE-FormalConjectures) ([upstream source](https://github.com/google-deepmind/formal-conjectures/blob/78bc92237b4bcf5ec812a52d07364aa74773bfe2/FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean)). The rest of this folder uses the collection's [MIT license](../LICENSE).
* [Prior-art audit](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers)
