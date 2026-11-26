# A conditional coordinate bound for field-priority ordinary F₄

Prioritizing the original `F₃` field equations as reducers keeps every temporary **individual variable exponent at most 5** inside a modified ordinary F₄ algorithm. This is a conditional mathematical bound, not a claim about the current solver: no code is changed here, the byte builds stay frozen, and any 4-bit nibble build must still keep its fail-closed checks above 15 (this note does not justify dropping those checks).

The bound applies only to individual variable exponents; total degree can grow much higher and needs separate storage and bounds checks.

## Precise hypotheses

Work in the ordinary polynomial ring `F₃[x1, ..., xn]` under any admissible monomial order, with original field equations `Fi = xi³ - xi`. Assume the working basis and all queued critical-pair references contain only original field equations (normalized to monic form) and "field-normal" polynomials whose **every monomial**, leading or tail, has every variable exponent at most 2.

Assume initial matrix seeds come strictly from ordinary S-pair multiples formed from the LCM of two such leading monomials, or unmultiplied basis rows during interreduction. Arbitrary normal-form queries, saturation multipliers, signature monomials, and other multiplication rules fall outside these hypotheses.

During symbolic preprocessing, whenever a column monomial `m` has any coordinate `mi >= 3`, reduce it with the field multiple

```
(m / xi³) * Fi = m - m / xi².
```

Keep these field reducers available even if the field polynomial was removed from the active reducer table. When all coordinates of `m` are at most 2, any field-normal basis reducer whose leading monomial divides `m` is allowed. Symbolic closure must process all tail columns introduced. An initial column already backed by a seed pivot does not need a duplicate field pivot, since its seed row obeys the bound below and its tail columns are still closed, provided every high-coordinate column has a valid pivot.

Linear algebra combines rows only over these existing columns, and new non-field basis rows come solely from non-pivot columns (which are all field-normal). Any intermediate interreduction before resuming pair generation must maintain this basis invariant.

## Proof of the temporary coordinate bound

For a normal-normal S-pair, let `a` and `b` be the leading exponent vectors and `t` any tail term of the first polynomial. Since every entry is at most 2, every coordinate in the pair multiple satisfies

```
max(a_j, b_j) - a_j + t_j <= 4.
```

For a field-normal S-pair involving `Fi`, only coordinate `i` can rise on the normal polynomial's side:

```
3 - a_i + t_i <= 5,
```

while all other coordinates stay at most 2. The `Fi` side has coordinates at most 3, and field-field pairs also have coordinates at most 3 (a total degree of 6 does not mean any single exponent reaches 6). Every seed monomial, including terms hashed into the table and later dropped, therefore has every coordinate at most 5.

Now take any column `m` added during symbolic closure. If `m` has some coordinate `>= 3`, its priority field row holds only `m` and `m / xi²`, which drops one coordinate by 2 and raises none. If `m` is field-normal, any normal reducer with leading vector `a` and tail term `t` gives

```
m_j - a_j + t_j <= 4.
```

By induction over symbolic closure, every column keeps coordinates at most 5. Every reducer row has tail monomials strictly below its leading monomial in the monomial order, and Gaussian elimination creates no new columns. Because every column with a coordinate `>= 3` receives a pivot, all new basis rows from the non-pivot block have coordinates at most 2, preserving the invariant for the next F₄ round.

Final interreduction begins from unmultiplied field-normal polynomials and original field rows (coordinates at most 3), so the same induction lowers the bound to **4** during interreduction. This covers all symbolic columns, including unused ones and any promoted during export, though it does not allow resuming pair generation from unfiltered auxiliary rows with non-normal leading monomials.

The bound 5 is tight: the raw S-pair multiple of `Fy = y³ - y` and `g = x² + y²` multiplies `g` by `y³` and hits `y⁵`. Although their leading monomials are coprime so Buchberger's product criterion can drop this pair before building it, the proof does not depend on that criterion and stays valid even if the pair is built.

Under degree-compatible orders such as DRL, total degree satisfies the separate bound `max(6, 2*n + 1)`, which does not fit in 3 bits.

## Why arbitrary reducer priority does not prove five

Under DRL with `x > z > w > y`, take the field-normal polynomials

```
A = x²*z² + x²*y²,
B = z²*w²*y² + 1,
C = x²*w + w*y².
```

The ordinary `(A, B)` pair multiple of `A` contains `m = x²*w²*y⁴`. Reducing `m` by `C` instead of `Fy` creates

```
y⁴*w*C = x²*w²*y⁴ + w²*y⁶,
```

reaching coordinate 6. Here `LM(A)` and `LM(B)` are not coprime, and `LM(C)` divides neither. Field priority instead produces `m - x²*w²*y²`, avoiding any exponent growth. This local symbolic example shows why the priority rule is essential (without claiming it occurs in the current solver's scheduler).

## Ordinary Gröbner correctness is an additional obligation

Bounding exponents does not by itself prove Gröbner-basis correctness if critical-pair management changes. The safest design keeps every `Fi` in the **logical** basis and critical-pair universe (even if active reducer scans or final output minimization hide redundant rows), applying only standard Buchberger criteria under their normal hypotheses. Cached field multiples are then valid multiples of basis elements, so standard pair completion still proves the Gröbner-basis property.

Removing a logical field generator requires a sound pair-update proof; checking only that some active leading monomial divides `xi³` is broken. For example, over `F₃`,

```
F = x³ - x,  G = x² + 1,
S(F, G) = x,  S(G, x) = 1.
```

The ideal is the unit ideal (0 solutions). Dropping `F` from critical pairs just because `LM(G)` divides `x³`, while using `F` only occasionally as a high-column reducer, skips `S(F, G)` and leaves `{G}` alone. Treating `{F, G}` as a Gröbner basis would wrongly count 2 standard monomials (`1, x`). Any implementation must preserve all required field critical pairs or prove each skipped pair redundant.

Final interreduction also has a self-reduction trap: if the input is just `F = x³ - x`, reducing `F` against a cached copy of `F` yields 0 and deletes the entire ideal. Field rows must stay logically protected against self-cancellation during reduction and output minimization.

Similarly, displacing an existing upper seed row with a priority field row must preserve row span (for instance by moving the displaced row into the target block) while keeping one triangular pivot per leading column.

## Source ownership and stage obligations for a future implementation

In the frozen checked-byte code, `multiplied_poly_to_matrix_row` copies `poly[COEFFS]`, indexing into basis coefficient arrays read later during linear algebra. A cached pointer into `bs->hm` is therefore not self-contained: basis compaction, sorting/reindexing, `free_basis_elements`, hash resets, exponent-slab reallocations, and staging can all invalidate row pointers, coefficient indices, monomial IDs, or exponent pointers.

A future implementation would need either immutable, lifetime-managed field-domain storage with a stable coefficient owner, or fresh construction of the two-term row `m - m/xi²` against the active monomial table and a fixed coefficient pool. Standalone copies must never keep stale basis coefficient indices, canonical monomials must be resolved again after hash resets, and raw pointers into reallocatable exponent slabs must never be cached.

Arithmetic remains ordinary polynomial arithmetic: priority reduction adds valid field-multiple rows without collapsing monomials inside the hash table, changing divisibility/LCM rules, or swapping ordinary Gröbner reduction for a quotient-ring heuristic.

Because seed construction, symbolic closure, final interreduction, auxiliary column promotion, and resumed basis insertion all touch these invariants and ownership rules, implementing this takes far more than changing reducer scan order. Any such change would need a full code review, small-ideal tests, ordinary basis checks, and packing-overflow guards. Three-bit packing is only a potential future use of this conditional bound.

## Reproduction and limits

[exact_f3_priority_bounds.py](exact_f3_priority_bounds.py) and [exact_f3_priority_bounds.json](exact_f3_priority_bounds.json) exhaustively verify all scalar coordinate bounds, 2,592 four-variable priority-field steps, all field-field seed cases, the tight degree-5 seed, the degree-6 counterexample, the missing-pair unit-ideal trap, and the self-reduction identity, while recording hashes of the consulted C files for context only.

Run `python experiments/exact_f3_priority_bounds.py --check` to reproduce all checks. No native solver runs, no backend changes, and no unrestricted board count follows from this note.
