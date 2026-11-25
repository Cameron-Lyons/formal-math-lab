# Four disjoint linear sign branches

The full labeled count has the exact decomposition

```
N = N0 + N1 + N2 + N3.
```

Each Nk is the quotient dimension of one complete exported ordinary F₃ ideal.
The independent three-valued offset and two-valued sign are retained inside
every input, so there is **no additional multiplier or divisor**. The four
counts are unevaluated. Natural and minimum-fill order are alternative
representations of the same four branches, not eight contributions.

## Disjoint partition and exact reconstruction

Use the same pair as the quintic construction:

```
P0=(0,1,2,3),  P3=(3,6,7,8),
Delta(z)=pattern(P0,z)−pattern(P3,z),  in T,L,M,R order.
```

On every valid board the two patterns differ, so Delta is nonzero. Let k be
its first nonzero coordinate, and define

```
a=z_apex,  D=z−a,  s=Delta_k(D),  d=s*D.
```

The sign belongs to {1,−1}, hence s²=1. The canonical board d has apex zero,
Delta_i(d)=0 for i<k, and Delta_k(d)=1. Conversely, given such a canonical
d and independent a∈F₃ and s∈{1,−1}, set

```
z_cell=a+s*d_cell.
```

The recovered board has first nonzero difference at exactly k; its recovered
sign is s. These constructions are inverse. Therefore the four images are
disjoint, exhaustive, and contain each labeled board exactly once.

Affine palette changes preserve native validity. Translation is already
separated in the frozen source. Under negation, each moment scales by its
total-degree parity, and the sole nonzero target is even, at degree eight.
The elementary-cubic zero equations also remain satisfied. Every coupled
source polynomial has uniform degree parity after field reduction; the
exporter checks this directly.

Every variable retains its individual field equation, so all quotients are
finite products of F₃ and their dimensions count points without multiplicity.
On branch k the exact algebra factorization is

```
A_k ≅ F₃[a]/(a³−a) ⊗ F₃[s]/(s²−1) ⊗ A_canonical,k.
```

The extra equation s³−s is retained explicitly for input compatibility and
is redundant by the ordinary identity s³−s=s(s²−1).

## Four sparse linear systems

In the frozen natural prefix order the selected difference forms are

```
Delta_T = 2*x1,
Delta_L = 2*x16 + 2*x71 + x72 + x94,
Delta_M = 2*x8 + 2*x9 + 2*x10,
Delta_R = 2*x1 + 2*x2.
```

For branch k impose the first k forms equal to zero and form k equal to one.
The corresponding coefficient and augmented ranks are both k+1. These
linear conditions are consistent in the ambient prefix space; this does not
establish a valid completion in any branch.

| Branch | First nonzero role | Added linear constraints | Terms in those constraints | Total generators |
|---|---|---:|---:|---:|
| 0 | T | 1 | 2 | 179 |
| 1 | L | 2 | 6 | 180 |
| 2 | M | 3 | 9 | 181 |
| 3 | R | 4 | 11 | 182 |

Every input has 97 variables: 95 canonical prefix coordinates, offset a at
zero-based index 95, and sign s at index 96. It contains the exact frozen
176 translated-plus-e3 source generators, then s³−s, s²−1, and its k+1 linear
conditions. No quintic selector is included. The source polynomial bodies
are preserved byte for byte, including in the minimum-fill variant.

Branch 0 directly fixes x1=2. Each branch introduces a nonzero target at
degree one, compared with degree five for the quintic selector and degree
eight for the original moment target. This may help early elimination, but
requires four complete counts. No basis performance has been measured.

## Exports and counting rule

The [manifest](exact_f3_sign_branches_manifest.json) lists all four branch
IDs, both input orders and hashes, the exact sum rule, and the completion
rule. The files are `exact_f3_sign_branch{k}_{natural,minfill}.ms`, with
adjacent JSON metadata. Each records the source hashes, all additional
polynomials, the coordinate map and bilinear original-color reconstruction.
Minimum-fill metadata includes both directions of its complete permutation.

An actual original-color fix must use `a+s*d_cell=color`. The known
81-cell, six-completion prefix has Delta=[1,2,0,2], hence k=0, a=1, s=1.
Its predicted dimensions are therefore `[6,0,0,0]` across the four branches.
These are deductions from the previously known prefix count; this exporter
does not run a solver or claim new fixed-prefix validation.

Report an unrestricted N only after obtaining a complete certified dimension
for every branch. Missing, partial or timed-out results are unknown, never
zero. Do not add both variable orders, and do not multiply a branch count by
six: the independent offset and sign factors are already present.

## Symmetry scope and checks

Every global palette permutation over F₃ is affine, z↦alpha*z+beta, with
alpha∈{1,−1}. It scales Delta by alpha and therefore preserves its first
nonzero coordinate. Palette symmetry gives no equality between different
branch counts.

Horizontal reflection changes P3 into P1 and swaps the lower left/right
roles. On existing valid witnesses, branch 0 reflects into both branches
0 and 1; branch 1 also reflects into both. The audit saves explicit valid
board pairs certifying this, so reflection does not uniformly exchange
those branch sets. No equality among branch counts, no impossibility of a
branch, and no more general symmetry obstruction is claimed.

The checker exhausts the 80 nonzero difference vectors. Their branch sizes
are 54,18,6,2, and their normalized difference-vector sizes are 27,9,3,1.
These numbers are **not board-count proportions**. It also independently
checks geometric validity and canonical roundtrips for 161 existing boards,
including all six affine palettes, and checks five complete polynomial
fixtures. Those stored witnesses happen to occupy branches 0 and 1 only
(12 and 149 respectively); absence of branches 2 and 3 is not evidence that
their unrestricted counts vanish.

Run `python experiments/exact_f3_sign_branches.py --check` to reproduce the
[audit](exact_f3_sign_branches_audit.json), all eight complete inputs, exact
source-body retention, all 97 field domains, linear ranks, inverse
permutations, finite partition and witness checks. No backend or earlier
frozen model is changed, and no solver is invoked.
