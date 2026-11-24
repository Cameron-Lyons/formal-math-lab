# Erdős #677 — Equal LCMs of disjoint blocks

Write $M(n,k)$ for the LCM of $n+1,\ldots,n+k$. Erdős #677 asks whether $M(m,k)\ne M(n,k)$ whenever $k>0$ and $m\ge n+k$. The general question remains open. The definitions here match the published Lean statement. [Problem status](https://erdosproblemaday.com/problem/677) · [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean)

## Results

At length two the LCM strictly increases with the start. Lengths three and four are settled in Lean with no external computation: for distinct starts the only equalities are $M(2,3)=M(3,3)=60$ and $M(1,4)=M(2,4)=60$, and both pairs of blocks overlap. [Length-three and length-four proofs](LengthThreeAndFour.md)

At length five, Lean rules out disjoint collisions for 87 of the 144 ordered residue pairs modulo 12 and for all reduced slopes of height at most $3\cdot10^{12}$. [Length-two and length-five proofs](LengthTwoAndFive.md)

**Length six is settled by a computer-assisted proof.** For arbitrary distinct starts, the only equalities are the three overlapping pairs with parameters $(3,4)$, $(5,6)$, and $(13,15)$. Lean verifies the reduction, the finite LCM checks, and the disjoint-block conclusion given the explicit affine bound. The proof of that bound uses elliptic logarithms and external arithmetic. [Proof, complete integral-point lists, and reproduction commands](cubic/LengthSix.md)

| Range | Verification |
| --- | --- |
| All lengths, later endpoint $m+k\le1000$ | Lean kernel, `no_collision_through_1000` |
| All lengths, start difference $m-n\le52$, with arbitrary starts | Lean kernel, `no_collision_shift_le_52` |
| Lengths 5 and 6, earlier parameter $n\le10^{20}$, with arbitrary later start | Lean kernel, `no_collision_five_six` |
| All lengths, later endpoint $m+k\le10{,}000{,}000$ | Exhaustive C++ search |
| All lengths, start difference $m-n\le7000$, with arbitrary starts | Lean kernel reduction to the C++ search |
| Lengths 5 and 6, earlier parameter $n\le10^{1000}$, with arbitrary later start | Exact Python search |
| Lengths 7 through 24, earlier parameter $n\le10^{100}$, with arbitrary later start | Exact Python search |
| Lengths 25 through 28, earlier parameter $n\le10^{20}$, with arbitrary later start | Exact Python search |

Lean also proves the conjectured inequality for adjacent blocks of all lengths, for every earlier block starting at 1, and for every positive shift divisible by all the integers from 1 to $k-1$.

## Lean declarations

- `Erdos677.three_collision_iff` and `Erdos677.four_collision_iff` classify the equal LCMs at lengths three and four.
- `Erdos677.erdos_677_two`, `Erdos677.erdos_677_three` and `Erdos677.erdos_677_four` are the conjectured inequality at lengths two, three and four.
- `Erdos677.six_collision_on_cubics` sends a repeated length-six LCM to one of four plane cubics.
- `Erdos677.six_collision_iff_three_of_affine_cover` gives the three pairs from the complete integral-point list.
- `Erdos677.no_collision_six_of_affine_bound` excludes disjoint blocks from the analytic bound alone.

For length six, the Lean sources specify both hypotheses explicitly. The arithmetic scripts verify the global bound and enumerate the integral points. [Lean declarations](SixCubics.lean) · [Reproduce the arithmetic](cubic/LengthSix.md#reproduction)

## Verification

Run the following from this directory with Elan installed.

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

A prime power divides a block LCM exactly when it divides an entry. If the later block contains a number that is itself a prime power, that power exceeds every earlier entry. The C++ search discards those later blocks. For the others it sums fixed 64-bit weights for the prime powers above $k$ that occur in each block. Equal LCMs always have equal sums. The program retains every matching pair for exact comparison, including any accidental matches between distinct LCMs. [Lean criterion](PrimePowers.lean)

Each prime power of a common LCM divides a positive difference between entries. For start difference $d$, all differences lie in $[d-k+1,d+k-1]$. Applying upper and lower binomial bounds to these two intervals gives an inequality that Lean checks for each length through 7,000. [Binomial bounds](BinomialBounds.lean) · [Displacement proof](Displacement.lean)

Each block LCM has the form $t k\binom{n+k}{k}$, where $t$ divides $M(0,k)/k$. For lengths five and six this leaves seven and four possible ratios of block products, respectively. For each ratio the two doubled centers lie in a narrow band around a line of algebraic slope. Lean verifies rational bounds for that slope and checks every integer point between them. A separate Python implementation uses exact integer arithmetic to extend the search. [Ratio reduction](FixedLength.lean) · [Lean checker](Height.lean) · [Python search](search/height.py)

## Attribution

[UpstreamInterval.lean](UpstreamInterval.lean) reproduces the Formal Conjectures definition of `Finset.lcmInterval` under its [Apache-2.0 license](LICENSE-FormalConjectures). The rest of the project uses the collection’s [MIT license](../LICENSE). [Upstream source](https://github.com/google-deepmind/formal-conjectures/blob/78bc92237b4bcf5ec812a52d07364aa74773bfe2/FormalConjecturesForMathlib/Algebra/GCDMonoid/Finset.lean) · [Dated prior-art audit](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers)
