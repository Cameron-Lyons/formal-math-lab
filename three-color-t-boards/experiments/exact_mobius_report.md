# Möbius aggregation for distinct T patterns

The method gives an exact characteristic polynomial and substantial small-board
compression. It has **not evaluated the unrestricted ten-row ternary count**.
Explicit enumeration of individual nonzero closure states has a rigorous lower
bound of **82,864,869,804 states** at height ten. Coarser symbolic aggregation is
not excluded by that bound, but component counts and component-size shapes do
not retain enough information for the next collision update.

## Exact closure reduction

Number rows and columns from zero and flatten cell `(r,j)` to `r²+j`. The
placement with lower row `r` and starting column `j` has ordered cells

\[
W_{r,j}=((r-1)^2+j,r^2+j,r^2+j+1,r^2+j+2),
\quad 1\le r<h,\quad 0\le j<2r-1.
\]

There are `n=h²` cells and `m=(h−1)²` placements. Let `P_h(q)` count boards whose
placement patterns are pairwise distinct. For a partition `π` of the placements,
let `λ(π)` identify corresponding cell roles of all placements in each block.
Write `c(λ)` for its number of cell classes. Partition-lattice inversion gives

\[
P_h(q)=\sum_{\pi\in\Pi_m}
 \left[\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!\right]q^{c(\lambda(\pi))}.
\]

This is a polynomial identity for every nonnegative integer `q`; it does not
need a finite-field characteristic restriction. When `h=q²+1`, distinctness
is exact coverage, so the requested answer is `P_10(3)`.

Define `C(π)` by grouping placements whose four cell-class labels under `λ(π)`
are identical. This is an extensive, monotone, idempotent closure operator, and
`λ(C(π))=λ(π)`. Thus generated cell partitions are in bijection with closed
placement partitions. If `L` is this closure lattice, then

\[
w(\rho):=\sum_{C(\pi)=\rho}\mu_{\Pi_m}(0,\pi)=\mu_L(0,\rho).
\]

Indeed, for a closed `ρ`, `C(π)≤ρ` is equivalent to `π≤ρ`. Consequently
`Σ_{τ≤ρ}w(τ)=Σ_{π≤ρ}μ_Π(0,π)=1[ρ=0]`, the defining recurrence for `μ_L`.
This proves the exact compressed expression

\[
P_h(q)=\sum_{\rho\in L}\mu_L(0,\rho)q^{c(\lambda(\rho))}.
\]

This is a subspace arrangement inside the braid arrangement: each collision
event is the intersection of four coordinate-equality hyperplanes. In the
edge-colored hypergraphic representation, cells are vertices and the aligned
equality edges of one collision share one edge color. Miller and Wakefield's
Proposition 3.7 gives deletion–contraction by an entire edge color, and Theorem
3.8 identifies its coloring polynomial with the arrangement characteristic
polynomial. Their contraction identifies each equality component, exactly the
operation used here. This supplies the relevant general theorem, rather than
an ordinary graph-coloring interpretation. [Primary source: *Edge Colored
Hypergraphic Arrangements*, §§2–3](https://arxiv.org/pdf/0903.4221).

## Evaluated small polynomials

Direct enumeration of placement partitions gives

\[
\begin{aligned}
P_1(q)&=q,\\
P_2(q)&=q^4,\\
P_3(q)&=q^9-6q^5+2q^3+9q^2-6q,\\
P_4(q)&=q^{16}-36q^{12}+19q^{10}+88q^9+374q^8-220q^7\\
 &\quad-889q^6+449q^5-834q^4+1426q^3+400q^2-778q.
\end{aligned}
\]

| Height | Placement partitions | Distinct cell closures | Nonzero closure weights | `P_h(2)` | `P_h(3)` |
|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 2 | 3 |
| 2 | 1 | 1 | 1 | 16 | 81 |
| 3 | 15 | 15 | 15 | 360 | 18,342 |
| 4 | 21,147 | 3,269 | 3,145 | 5,756 | 28,174,794 |

The evaluations agree with the independent exhaustive board census. A second
implementation processes pair-collision events by signed deletion–contraction
and aggregates equal cell partitions. It independently reproduces `P_4` and
all 3,145 nonzero closures in approximately 0.024 seconds.

For heights three and four, division by `q(q−1)` leaves irreducible polynomials
over the rationals: the degree-seven quotient is irreducible modulo 7 and the
degree-fourteen quotient is irreducible modulo 3. The standalone checker
verifies this without a computer-algebra dependency, using the Frobenius/gcd
criterion for irreducibility over a finite field. Thus neither small polynomial
has a further rational factorization. This is evidence about these two heights,
not a claim about factorization at height ten.

## The closure is not a matroid closure

At height four, placements in row-major order are indexed `0,…,8`. Equating
placements `0,…,6` produces the cell partition

`{0,…,13}, {14}, {15}`.

Let `a` be collision `0=8` and `b` collision `0=7`. Adding `a` merges all cells,
so implies `b`; adding `b` only merges cell 14 into the large class, so does not
imply `a`. Initially `b` is not implied. This violates the closure exchange
axiom: `b∈cl(S∪{a})\cl(S)` but `a∉cl(S∪{b})`. Therefore ordinary geometric-lattice
or matroid characteristic-polynomial machinery cannot be applied directly to
this collision closure. The broader subspace-arrangement theory still applies.

## Nonzero-state lower bound at height ten

Select placements with lower row

`r∈{1,3,5,7,9}` and starting column `j∈{0,3,6,…}∩[0,2r−2]`.

Their counts are `1+2+3+5+6=17`. These 17 T's are cell-disjoint. Their union has
68 cells and contains **no other complete T**:

* On a selected odd lower row, a top cell belongs to the union only at a
  selected starting column; hence a contained T is one of the selected T's.
* On an even lower row, the occupied cells are spaced three apart, so cannot
  contain a consecutive lower triple.

For any partition of the selected placements, equality identifications involve
only these 68 cells. Every unselected placement has an untouched singleton
cell. A fixed cell appears in at most one placement in any fixed role, so that
singleton prevents the unselected placement from becoming equal to another
placement. Therefore the closure-lattice interval below the state merging all
17 selected patterns is exactly `Π_17`.

Every state in this interval has nonzero Möbius value
`∏_B(−1)^(|B|−1)(|B|−1)!`. Hence the **final** closure sum contains at least

\[
B_{17}=82,864,869,804
\]

nonzero individual states. This is not merely a transient-state or
before-cancellation lower bound.

The bound applies specifically to algorithms that materialize individual
closure states. This interval alone aggregates immediately to

\[
q^{32}(q^4)_{17},
\qquad (x)_k=x(x-1)\cdots(x-k+1),
\]

so the bound does **not** establish that all Möbius or symbolic methods are
infeasible.

## Why the easy shape aggregation does not extend directly

Here placement indices are the flattened top-cell indices. Consider two states
from that same induced packing:

* `A`: impose collision `64=67`, the lower-row-nine windows starting at 0 and 3.
* `B`: impose collision `0=4`.

Both have 92 singleton cell classes and four classes of size two, hence 96
classes. Both have the same selected-placement partition shape (one pair and
15 singletons), and Möbius weight −1.

Now add the external collision `65=68`, the row-nine windows starting at 1 and
4. State `A` then has 94 cell classes, whereas state `B` has 92. In `A`, two
lower-role equalities are already implied by `64=67`; in `B`, all four new
equalities are independent. Therefore merging states solely by degree,
cell-component-size multiset, or selected-placement block-size multiset loses
information required for the next update. At this update their contracted
monomials have different degrees. Some spatial attachment data must survive.

An independently constructed example and checker from the parent investigation
are recorded in [exact_partition_coarsening.json](exact_partition_coarsening.json).
Neither example rules out every possible aggregation based on richer data or
a different recurrence.

## Bounded scaling experiment and artifacts

The C++ implementation processes collision pairs by increasing second placement
index, keeps only nonzero coefficients, and sets explicit state and time caps.
At height five it completed 71 of 120 collision events, retaining 480,058
nonzero states. Event 72 reached the 500,001-state cap after about 3.9 seconds.
The result is marked `INCOMPLETE`; it does not provide `P_5`.

The C++ program is restricted to at most 16 placements. Signed 64-bit
coefficients are sufficient: before cell aggregation, each prefix is a graph
of pair-equality events on the placements. Its absolute coefficient sum is
the number of acyclic orientations of that graph, at most `16!`, since a total
vertex order induces every acyclic orientation. Aggregation cannot increase
the absolute sum. During a partially applied update the bound is at most twice
that amount. Thus retained values and updates fit signed 64-bit arithmetic for
these bounded experiments.

Reproduction:

```sh
python experiments/exact_mobius_small.py --output experiments/exact_mobius_small_results.json
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_mobius_closure.cpp -o /tmp/exact_mobius_closure
/tmp/exact_mobius_closure 4 500000 30
/tmp/exact_mobius_closure 5 500000 30
python experiments/exact_mobius_check.py
```

The standard-library checker recomputes all small polynomials, compares the
saved independent C++ result, certifies modular irreducibility, and verifies
the exchange, packing, Bell-number, and shape-update witnesses. Results are in
[exact_mobius_check_results.json](exact_mobius_check_results.json). The raw
small-polynomial data are in
[exact_mobius_small_results.json](exact_mobius_small_results.json), and bounded
recurrence outputs are in
[exact_mobius_closure_h4.json](exact_mobius_closure_h4.json) and
[exact_mobius_closure_h5.json](exact_mobius_closure_h5.json), with accompanying logs.
