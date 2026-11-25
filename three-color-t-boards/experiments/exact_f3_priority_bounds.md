# A conditional coordinate bound for field-priority ordinary F₄

A modified ordinary F₄ algorithm can keep every temporary **variable
coordinate at most five** by prioritizing the original F₃ field reducers.
This is a conditional mathematical result, not a claim about the current
solver. No implementation is changed here. The existing byte builds remain
frozen, and a nibble implementation must retain its fail-closed checks above
15; this note supplies no bound-five justification for that implementation.

The result concerns individual variable exponents. Total degree can be much
larger and needs separate storage and checks.

## Precise hypotheses

Work in the ordinary polynomial ring F₃[x1,...,xn], with any fixed admissible
monomial order. Let Fi=xi³−xi be the original field equations. The working
basis and any retained pair references contain only original field equations
and polynomials whose **every monomial**, including its leading monomial,
has coordinates at most two. A nonzero scalar multiple of Fi can be normalized
once to the displayed monic form.

The only initial matrix seeds are ordinary S-pair multiples formed from the
LCM of two such leading monomials, or unmultiplied basis rows for an
interreduction. Arbitrary requested normal-form inputs, saturation multipliers,
signature monomials and other multiplication schemes are outside this result.

During symbolic closure, if a column monomial m has a coordinate mi≥3, use
the original field multiple

```
(m/xi³)*Fi = m − m/xi².
```

The original field reducer must remain available even when its basis row is
removed from an active reducer list. If every coordinate of m is at most two,
any normal basis reducer whose leading monomial divides m may be used.
Symbolic closure must process all introduced tail columns. An initial column
already backed by a seed pivot need not acquire a duplicate field pivot: its
seed row is independently bounded below, and its tail columns must still be
closed. There must be a valid pivot row for every high-coordinate column.

Coefficient elimination only combines rows on these existing columns.
New non-field basis polynomials must be emitted from the nonpivot columns,
which are all field-normal. Any intermediate interreduction that resumes
pair generation must restore this same basis invariant.

## Proof of the temporary coordinate bound

For a normal-normal pair, write leading exponent vectors a,b and a term t of
the first polynomial. All coordinates are at most two, so a term in its
ordinary pair multiple has coordinate

```
max(a_j,b_j) − a_j + t_j ≤ 4.
```

For a field-normal pair involving Fi, only coordinate i can be enlarged on
the normal-polynomial side:

```
3 − a_i + t_i ≤ 5.
```

All other coordinates on that side remain at most two. The field-polynomial
side has coordinates at most three. Field-field pair rows also have
coordinates at most three; their possible total degree six is not a
coordinate exponent six. Thus every seed monomial has coordinates at most
five, including terms inserted into a hash table but never ultimately used.

Now consider any column introduced during closure. If it has a coordinate
at least three, its priority field row contains exactly m and m/xi². The
latter lowers one coordinate by two and increases none. If m is field-normal,
a normal reducer with leading exponent vector a and tail vector t produces

```
m_j − a_j + t_j ≤ 4.
```

Induction over the complete symbolic closure gives the bound five. All rows
have strictly smaller tail monomials than their leading monomial under the
ordinary monomial order. Coefficient row operations introduce no new
monomials, so they preserve the bound. Every high column has a reducer pivot;
new right-block basis rows therefore have all coordinates at most two,
closing the induction between F₄ iterations.

Final interreduction starts from unmultiplied normal polynomials and original
field rows, whose coordinates are at most three. The same argument gives the
stronger bound **four** during that stage. This covers every symbolic column,
including unused columns and columns later promoted by an all-column export
path. It does not justify resuming pair generation from unfiltered auxiliary
multiple rows with nonnormal leading monomials.

The bound five is attained by the raw ordinary pair multiple of
`Fy=y³−y` and `g=x²+y²`: multiplying g by y³ introduces y⁵. Their leading
monomials are coprime, so an ordinary product criterion can discard this
particular pair before materialization. The stated bound does not depend on
that criterion and is safe if the pair is materialized.

For degree-compatible orders such as DRL, the separate total-degree bound is
`max(6,2*n+1)`: it bounds pair LCM degrees, initial tail degrees, and every
recursive reducer multiple. It is not a three-bit quantity.

## Why arbitrary reducer priority does not prove five

In DRL with variable order x>z>w>y, consider the field-normal polynomials

```
A = x²*z² + x²*y²,
B = z²*w²*y² + 1,
C = x²*w + w*y².
```

The ordinary A,B pair multiple of A contains m=x²*w²*y⁴. Selecting C to
reduce m produces the row

```
y⁴*w*C = x²*w²*y⁴ + w²*y⁶,
```

which has a coordinate six. The leading monomials of A and B are not
coprime, and LM(C) divides neither of them. Field priority instead introduces
`m−x²*w²*y²`, which does not increase a coordinate. This is a valid local
symbolic construction showing why the priority premise matters; it is not
claimed to be an actual trace of the current solver's degree scheduler.

## Ordinary Gröbner correctness is an additional obligation

The exponent argument alone does not validate a change to critical-pair
bookkeeping. A conservative correct design keeps every Fi in the **logical**
ordinary basis and ordinary pair universe, even if active reducer selection
or output minimization suppresses redundant rows. It may apply established
ordinary Buchberger criteria with their usual hypotheses. Cached field rows
can then be prioritized as legitimate multiples of logical basis elements.
All introduced rows remain in the original ideal, and complete ordinary pair
processing still supplies the ordinary Gröbner-basis criterion.

An alternative design may remove logical field generators only with a valid
ordinary ideal/pair-update argument. Merely preserving divisibility of each
cube by an active leading monomial is insufficient. For example,

```
F=x³−x,  G=x²+1,
S(F,G)=x,  S(G,x)=1   over F₃.
```

The ideal is the unit ideal and has zero solutions. Dropping F from the pair
universe because LM(G) divides x³, while keeping F only as an occasional
high-column reducer, never triggers this necessary pair in a basis consisting
of G alone. Mistaking {F,G} for a completed basis would count the two standard
monomials 1,x, which is wrong. The implementation must preserve field-related
critical-pair obligations or prove every skipped obligation validly redundant.

Final interreduction has a separate self-reduction hazard. If the input is
only F=x³−x, reducing that retained generator against its identical cached
copy gives zero. Discarding both would lose the original ideal. A field row
must remain logically represented, its own leading term must be protected
when appropriate, and final output minimization must preserve the ideal.

Likewise, replacing an already selected upper seed row by a priority field
row must not silently discard the old seed relation. Preserve the necessary
row span, for example by moving the displaced row to the target block, and
maintain one valid triangular reducer pivot per fixed leading column.

## Source ownership and stage obligations for a future implementation

The preserved checked-byte source uses basis-indexed coefficients in
`multiplied_poly_to_matrix_row`: a matrix row copies `poly[COEFFS]`, and later
linear algebra reads the corresponding basis coefficient array. A cached
pointer to an original `bs->hm` row is therefore not a self-contained field
reducer. Basis removal, sorting/reindexing, final `free_basis_elements`, hash
reset/rebuild, exponent-slab reallocations and staging can invalidate row
pointers, coefficient indices, monomial IDs or exponent pointers.

A future design needs either immutable, lifetime-managed original-domain
storage with an explicit compatible coefficient owner, or construction of
the exact two-term row `m−m/xi²` using the current monomial table and a stable
coefficient source. Standalone copies must not retain stale basis coefficient
indices. Canonical monomials must be reinserted or resolved after hash resets;
raw pointers into reallocatable exponent slabs must not be cached.

The arithmetic path remains ordinary polynomial arithmetic. The priority
rule adds valid field-multiple rows; it does not identify ordinary monomials
inside the hash table, change LCM/divisibility semantics, or silently replace
an ordinary Gröbner computation by a quotient-ring heuristic.

All seed construction, recursive closure, final interreduction, auxiliary
column promotion and any resumed basis insertion need the stated invariants.
The current source's already-marked leading columns and coefficient ownership
contracts make this more than a change to the reducer scan order. A new
implementation would need its own source review, complete tiny-ideal tests,
ordinary basis checks and packing-overflow guards. Three-bit storage is only
a possible future use of the conditional mathematical bound.

## Reproduction and limits

[The checker](exact_f3_priority_bounds.py) and [saved results](exact_f3_priority_bounds.json)
exhaust all scalar coordinate cases underlying the inequalities, 2,592
four-variable priority-field steps, and the field-field seed cases. They
also check the explicit degree-five seed, degree-six local counterexample,
missing-pair unit-ideal example and self-reduction identity. The JSON records
hashes of the source files consulted for ownership/call-path context only.

`python experiments/exact_f3_priority_bounds.py --check` reproduces the
results. No native solver is invoked, no backend is modified, and no result
about the unrestricted board count follows from this note.
