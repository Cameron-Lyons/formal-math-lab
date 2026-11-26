# Möbius aggregation for distinct T patterns

This method gives an exact characteristic polynomial and heavy compression on small boards, while **leaving the unrestricted ten-row ternary count unevaluated**. Any method that materializes individual nonzero closure states faces a rigorous lower bound of **82,864,869,804 states** at height 10. Coarser symbolic aggregation is not ruled out by that bound, though component counts and component-size shapes alone lose information needed for later collision updates.

## Exact closure reduction

Index rows and columns from 0 and flatten cell `(r, j)` to `r² + j`. The T placement on lower row `r` starting at column `j` has ordered cells

\[
W_{r,j}=((r-1)^2+j,r^2+j,r^2+j+1,r^2+j+2),
\quad 1\le r<h,\quad 0\le j<2r-1.
\]

There are `n = h²` cells and `m = (h - 1)²` placements. Let `P_h(q)` count `q`-colorings whose placement patterns are pairwise distinct. For a partition `π` of the placements, let `λ(π)` merge the corresponding four cell roles across every block of `π`, and let `c(λ)` be its number of cell classes. Möbius inversion on the partition lattice gives

\[
P_h(q)=\sum_{\pi\in\Pi_m}
 \left[\prod_{B\in\pi}(-1)^{|B|-1}(|B|-1)!\right]q^{c(\lambda(\pi))}.
\]

This polynomial identity holds for all nonnegative integers `q` with no finite-field restriction. When `h = q² + 1`, distinctness equals exact coverage, so the unrestricted ternary count is `P_10(3)`.

Define the closure `C(π)` by grouping placements whose four cell-class labels under `λ(π)` match. Because `C` is extensive, monotone, and idempotent with `λ(C(π)) = λ(π)`, reachable cell partitions correspond bijectively to closed placement partitions. On this closure lattice `L`,

\[
w(\rho):=\sum_{C(\pi)=\rho}\mu_{\Pi_m}(0,\pi)=\mu_L(0,\rho).
\]

For every closed `ρ`, `C(π) ≤ ρ` holds if and only if `π ≤ ρ`, so `Σ_{τ ≤ ρ} w(τ) = Σ_{π ≤ ρ} μ_Π(0, π) = 1[ρ = 0]`, matching the defining recurrence of `μ_L`. That proves the compressed formula

\[
P_h(q)=\sum_{\rho\in L}\mu_L(0,\rho)q^{c(\lambda(\rho))}.
\]

Geometrically, this is a subspace arrangement inside the braid arrangement: each T-collision intersects four coordinate-equality hyperplanes. Viewing cells as vertices and giving the four aligned equality edges of one collision a shared edge color puts this in the framework of Miller and Wakefield ([*Edge Colored Hypergraphic Arrangements*, Sections 2-3](https://arxiv.org/pdf/0903.4221)): Proposition 3.7 gives deletion-contraction by a whole edge color (identifying each equality component, exactly as above), and Theorem 3.8 matches the coloring polynomial to the arrangement's characteristic polynomial.

## Evaluated small polynomials

Direct enumeration of placement partitions gives:

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

These values match the independent exhaustive board census. A second implementation running signed deletion-contraction over collision pairs and merging equal cell partitions independently reproduces `P_4` and all 3,145 nonzero closures in about 0.024 seconds.

Dividing `P_3` and `P_4` by `q(q - 1)` leaves polynomials irreducible over `Q` (the degree-7 factor is irreducible mod 7, and the degree-14 factor is irreducible mod 3, checked directly by Frobenius/gcd with no CAS dependency). Neither small polynomial factors further over `Q`, without saying whether `P_10` factors.

## The closure is not a matroid closure

At height 4, index placements `0, ..., 8` in row-major order. Merging placements `0, ..., 6` produces cell partition

`{0, ..., 13}, {14}, {15}`.

Let `a` be collision `0 = 8` and `b` be collision `0 = 7`. Adding `a` merges all cells and therefore implies `b`, while adding `b` only absorbs cell 14 and does not imply `a` (and `b` was not implied initially). This breaks the matroid exchange axiom (`b ∈ cl(S ∪ {a}) \ cl(S)` yet `a ∉ cl(S ∪ {b})`), so geometric-lattice/matroid theorems do not apply directly, though general subspace-arrangement theory still holds.

## Nonzero-state lower bound at height ten

Pick the placements with lower row `r ∈ {1, 3, 5, 7, 9}` and starting column `j ∈ {0, 3, 6, ...} ∩ [0, 2r - 2]`. There are `1 + 2 + 3 + 5 + 6 = 17` such placements; they are pairwise cell-disjoint, cover 68 cells, and contain **no other complete T**:

* On a chosen odd lower row, top cells inside the 68-cell union occur only at chosen starting columns, so every T there is already one of the 17.
* On an even lower row, chosen cells are spaced 3 apart, leaving no three consecutive lower cells.

Any partition of these 17 placements only touches those 68 cells, leaving every unselected placement with at least one untouched singleton cell. Because a cell can appear in at most one placement in any fixed role, that singleton stops any unselected placement from colliding with another placement. Thus the closure-lattice interval below merging all 17 placements is isomorphic to `Π_17`.

Every partition in `Π_17` has nonzero Möbius weight `∏_B (-1)^(|B| - 1)(|B| - 1)!`, so the **final** closure sum has at least

\[
B_{17}=82,864,869,804
\]

nonzero states (not just transient pre-cancellation states).

This lower bound targets explicit state materialization only. On its own, that entire `Π_17` interval sums symbolically to

\[
q^{32}(q^4)_{17},
\qquad (x)_k=x(x-1)\cdots(x-k+1),
\]

so it does **not** prove all Möbius or symbolic approaches are infeasible.

## Why the easy shape aggregation does not extend directly

Indexing placements by their flattened top-cell index, compare two states inside that 17-placement packing:

* `A`: collision `64 = 67` (row-9 windows starting at 0 and 3).
* `B`: collision `0 = 4`.

Both states have 92 singleton cell classes and 4 classes of size 2 (96 classes total), the same placement-partition shape (one pair, 15 singletons), and Möbius weight `-1`.

Now add collision `65 = 68` (row-9 windows starting at 1 and 4). State `A` drops to 94 cell classes (two lower equalities were already implied by `64 = 67`), whereas state `B` drops to 92 (all four new equalities are fresh), giving different contracted monomial degrees. Grouping states solely by degree, cell-class-size multiset, or placement-block-size multiset therefore throws away spatial attachment data needed for later steps.

An independent example and checker live in [exact_partition_coarsening.json](exact_partition_coarsening.json). Richer invariants or a different recurrence remain open.

## Bounded scaling experiment and artifacts

The C++ closure solver processes collision pairs ordered by their second placement index, discards zero coefficients, and enforces state and time caps. At height 5 it finished 71 of 120 collision events with 480,058 nonzero states, then hit its 500,001-state cap on event 72 after ~3.9 seconds, stopping as `INCOMPLETE` (so `P_5` is not computed here).

The C++ solver caps inputs at 16 placements so signed 64-bit integers cannot overflow: before cell merging, each prefix of collision pairs forms a graph whose absolute coefficient sum equals its number of acyclic orientations (at most `16!`), cell aggregation cannot raise that sum, and intermediate updates at most double it.

Reproduction:

```sh
python experiments/exact_mobius_small.py --output experiments/exact_mobius_small_results.json
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror experiments/exact_mobius_closure.cpp -o /tmp/exact_mobius_closure
/tmp/exact_mobius_closure 4 500000 30
/tmp/exact_mobius_closure 5 500000 30
python experiments/exact_mobius_check.py
```

The standard-library checker recomputes `P_1..P_4`, compares the saved C++ output, verifies modular irreducibility, and checks the exchange, packing, Bell-number, and shape-update witnesses ([exact_mobius_check_results.json](exact_mobius_check_results.json)). Raw small-polynomial data are in [exact_mobius_small_results.json](exact_mobius_small_results.json), and bounded C++ outputs are in [exact_mobius_closure_h4.json](exact_mobius_closure_h4.json) and [exact_mobius_closure_h5.json](exact_mobius_closure_h5.json) with their logs.
