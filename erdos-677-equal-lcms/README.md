# Erdős Problem #677: equal LCMs of consecutive integers

Write $M(n, k) = \operatorname{lcm}(n + 1, n + 2, \ldots, n + k)$ for the least common multiple of $k$ consecutive positive integers. Erdős Problem #677 asks whether $M(m, k) \ne M(n, k)$ whenever $k > 0$ and $m \ge n + k$, meaning two disjoint blocks of the same length never share an LCM. The general problem is still open.

This Lean 4 project classifies all equal LCMs for lengths $k = 2, 3, 4$ purely inside Lean, gives a computer-assisted classification for $k = 6$ (Lean reduction plus external elliptic-curve arithmetic), and proves bounds on shifts, endpoints, and heights. The definitions match `FormalConjectures/ErdosProblems/677.lean`.

| Field | Summary |
| --- | --- |
| Problem | Erdős Problem #677 (`erdosproblems.com/677`), equal LCMs of consecutive integers $M(m, k) = M(n, k)$, `FormalConjectures/ErdosProblems/677.lean` |
| Status | Lengths $k = 2, 3, 4$ proved in Lean 4; length $k = 6$ settled with external elliptic-curve arithmetic for the affine bound (Lean checks the reduction and finite cases). General $k$ is still open. |
| Classifications | For distinct starts $m > n$: $k = 2$, none; $k = 3$, only $(n, m) = (2, 3)$ ($\operatorname{lcm} = 60$, overlapping); $k = 4$, only $(1, 2)$ ($\operatorname{lcm} = 60$, overlapping); $k = 6$, only $(3, 4)$, $(5, 6)$, $(13, 15)$ (all overlapping). |
| Main theorems | `Erdos677.erdos_677_two`, `erdos_677_three`, `erdos_677_four`, `three_collision_iff`, `four_collision_iff`, `six_collision_iff_three_of_affine_cover`, `no_collision_shift_le_52` |
| Verification | `lake exe cache get && lake build` (Lean 4.36.0 + mathlib); see [cubic/LengthSix.md](cubic/LengthSix.md#reproduction) for length-6 elliptic-curve arithmetic |
| Prior art | Checked 23-24 November 2026. The classifications at $k = 3, 4$, the three overlapping pairs at $k = 6$, and the four-cubic reduction were known earlier. No earlier Lean proof for $k = 3$ or $k = 4$, nor a complete integral-point proof for $k = 6$, was found (priority unverified). See [PRIOR_ART.md](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers). |

## Results

* Length $k = 2$: $M(n, 2) = (n+1)(n+2)$ strictly increases with $n$, so no collisions occur (`Erdos677.erdos_677_two`).
* Lengths $k = 3$ and $k = 4$ (pure Lean 4): for distinct starts, the only equalities are $M(2, 3) = M(3, 3) = 60$ and $M(1, 4) = M(2, 4) = 60$. Both pairs overlap, so no disjoint blocks have equal LCM ([LengthThreeAndFour.md](LengthThreeAndFour.md)).
* Length $k = 5$: Lean rules out disjoint collisions for 87 of the 144 ordered residue pairs modulo 12 and for all reduced slopes of height at most $3 \cdot 10^{12}$ ([LengthTwoAndFive.md](LengthTwoAndFive.md)).
* Length $k = 6$ (computer-assisted): for distinct starts, the only equalities are the three overlapping pairs $(n, m) \in \{(3, 4), (5, 6), (13, 15)\}$. Lean checks the reduction to four plane cubics, the finite LCM cases, and the disjoint-block conclusion given the affine bound. External scripts using elliptic logarithms and David's theorem prove the affine bound and list all integral points ([cubic/LengthSix.md](cubic/LengthSix.md)).
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
* `Erdos677.no_collision_six_of_affine_bound` rules out disjoint length-6 blocks from the analytic affine bound alone.

For length 6, the Lean files state both hypotheses explicitly, and the external scripts prove the global bound and list the integral points ([SixCubics.lean](SixCubics.lean), [reproduction notes](cubic/LengthSix.md#reproduction)).

## Proof methods and verification

Run from this directory with `elan` installed (pinned Lean 4.36.0):

```sh
lake exe cache get
lake build
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror search/search.cpp -o /tmp/erdos677-search
/tmp/erdos677-search 10000000
python search/displacement.py
python search/height.py --exponent 1000 5 6
python search/height.py --tight-bound --exponent 100 7 8 9 10 11 12 13 14 15 16
python search/height.py --coefficient-sieve --exponent 100 17 18 19 20 21 22 23 24
python search/height.py --coefficient-sieve --exponent 20 25 26 27 28
python -m unittest discover -s search
```

* Prime-power filter ([PrimePowers.lean](PrimePowers.lean)): a prime power divides a block LCM if and only if it divides some entry. If the later block itself contains a prime power, that power is larger than every entry in the earlier block, so the C++ search skips it. For the remaining blocks, the search hashes prime powers above $k$ and checks exact matches.
* Displacement bounds ([BinomialBounds.lean](BinomialBounds.lean), [Displacement.lean](Displacement.lean)): every prime power dividing a common LCM must divide a positive difference between entries from the two blocks. For shift $d = m - n$, those differences lie in $[d - k + 1, d + k - 1]$. Binomial bounds on these intervals give an inequality checked in Lean through $d \le 7000$.
* Slope and height bands ([FixedLength.lean](FixedLength.lean), [Height.lean](Height.lean), [search/height.py](search/height.py)): each block LCM has the form $t k \binom{n+k}{k}$ with $t \mid M(0, k)/k$. For lengths 5 and 6, this leaves seven and four possible product ratios, confining the doubled block centers to narrow bands around lines of algebraic slope. Lean checks these bands, and exact Python arithmetic extends the range.

## References and attribution

* [Erdős Problems #677](https://www.erdosproblems.com/677) and [Erdős Problem a Day #677](https://erdosproblemaday.com/problem/677)
* [Formal Conjectures `ErdosProblems/677.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean)
* [UpstreamInterval.lean](UpstreamInterval.lean) reproduces the Formal Conjectures definition of `Finset.lcmInterval` under its [Apache-2.0 license](LICENSE-FormalConjectures) ([upstream source](https://github.com/google-deepmind/formal-conjectures/blob/78bc92237b4bcf5ec812a52d07364aa74773bfe2/FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean)). The rest of this folder uses the collection's [MIT license](../LICENSE).
* [Prior-art audit](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers)
