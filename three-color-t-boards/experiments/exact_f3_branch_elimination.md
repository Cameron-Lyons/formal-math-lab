# Exact affine elimination of the four linear sign branches

The four branch equations can be eliminated without changing any branch
count. The resulting inputs have **96, 95, 94, and 93 variables**, respectively,
and retain both independent symmetry factors. Their quotient dimensions are
N0,N1,N2,N3, whose sum is the full labeled count N. No dimension is evaluated
here, and no additional multiplier is appropriate.

## Exact polynomial-ideal reduction

Start with the four frozen [linear sign branches](exact_f3_sign_branches.md).
In branch k, the k+1 affine equations have rank k+1. Gaussian elimination
solves selected coupled prefix variables as affine expressions L in the
remaining coordinates. The offset a and sign s are never selected as pivots.
The quotient by these affine equations is isomorphic to the polynomial ring
in the remaining variables, by substitution and inverse coordinate projection.

The field domains behave particularly simply over F₃. For any affine form
L=c+sum(a_i*y_i), with c,a_i in F₃, the ordinary polynomial identity is

```
L³−L = sum_i a_i*(y_i³−y_i).
```

The constant disappears because c³=c, and the coefficients satisfy a_i³=a_i.
Thus every eliminated field domain follows from the surviving individual
field domains. The checker expands each identity as an ordinary polynomial,
before any field reduction. There is no need for an extra pivot-domain
constraint or an extension-field parameter.

After substitution, reducing each source moment and elementary cubic
modulo y_i³−y_i preserves its ideal together with the retained domains.
All 76 source moments and four elementary cubics survive as nonzero
polynomials. The exporter independently regenerates all 80 nonconstant
geometric moments in the new affine color coordinates: the four unary
linear moments remain identically zero, and the other 76 match the source
images exactly. It also checks all four elementary-cubic images against
fresh geometric expansions.

Consequently the complete reduced ideal is isomorphic to its original
branch ideal. It contains every remaining individual field equation,
including a³−a and s³−s, plus s²−1. These squarefree split field domains
make the quotient a product of copies of F₃; its dimension counts solutions
without multiplicity. Each branch still counts full labeled boards in its
original first-nonzero-difference class.

## Selected affine substitutions

The following x indices are **one-based indices in the old 97-variable
natural-order input**, not the compacted output indices:

| Branch | Eliminated old variables and replacements |
|---|---|
| 0 | x1=2 |
| 1 | x1=0; x72=1+x16+x71+2*x94 |
| 2 | x1=0; x72=x16+x71+2*x94; x9=2+2*x8+2*x10 |
| 3 | x1=0; x72=x16+x71+2*x94; x9=2*x8+2*x10; x2=2 |

The generator exhausts every independent coordinate pivot set of each
branch's affine equations: 1, 4, 12, and 12 choices. It selects the smallest
total moment-plus-e3 support, breaking ties by largest individual support
and then pivot tuple. This is an optimum within these coordinate pivot
sets, not among general changes of coordinates or algebraic representations.

| Branch | Variables | Coupled variables | Generators | Moment terms | e3 terms | Total terms |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 96 | 94 | 177 | 95357 | 566 | 96117 |
| 1 | 95 | 93 | 176 | 97925 | 620 | 98737 |
| 2 | 94 | 92 | 175 | 97832 | 632 | 98654 |
| 3 | 93 | 91 | 174 | 95216 | 602 | 96006 |

The source has 96056 coupled terms. Eliminating branch equations decreases
this slightly in branches 0 and 3 and increases it modestly in branches
1 and 2. The calculation removes solved variables from the basis problem;
no solver performance improvement is asserted.

## Complete exports, maps and certificates

The [manifest](exact_f3_branch_elimination_manifest.json) lists the eight
inputs `exact_f3_branch_elimination_k{k}_{natural,minfill}.ms` and their
adjacent JSON metadata. Each branch has two alternative variable orders.
Natural order retains surviving old indices in ascending order; minimum-fill
order filters the earlier frozen permutation by the same pivot set. The
independent offset and sign remain the final two variables in both.

Each complete input contains, in order:

1. Every remaining individual field cubic.
2. The 76 substituted and field-reduced moments.
3. The four substituted and field-reduced elementary cubics.
4. The independent equation s²−1.

Metadata records the exact new-to-old coordinate projection and all 97 old
variables as affine polynomials in the new ring. It also records the 100
canonical colors as **affine** forms and the 100 actual colors as polynomials
of degree at most two. In particular,

```
z_cell = a+s*d_cell
```

can now include a term proportional to s when d_cell has a nonzero constant.
Using only a linear part of d_cell would impose the wrong original-color
fixes. The inverse still recovers a from the original apex, the branch k and
s from the selected pattern difference, then d=s*(z−a), its Gray prefixes,
and the retained coordinates.

Every source generator has a recorded image certificate. Eliminated field
domains have explicit ordinary affine-domain identities; surviving domains
point to their new input index; all moments and elementary cubics have
image hashes; the removed branch equations are checked to vanish as
ordinary affine identities. The domain-combination coefficients are
explicitly labeled in old97 source coordinates. No source generator is
silently discarded.

The natural and minimum-fill outputs are checked by inverse polynomial
renaming. Both put field equations in ascending variable order, so this
also permutes the initial domain-generator block; the audit records that
complete generator permutation.

## Checks and counting scope

Run `python experiments/exact_f3_branch_elimination.py --check` to reproduce
the [audit](exact_f3_branch_elimination_audit.json), all input hashes, the
pivot comparisons, ordinary identities and fresh geometric polynomial
checks. Eight arbitrary assignments per branch check the affine coordinate
bijections; these are coordinate tests, not claimed valid boards. Existing
valid witnesses round-trip in their actual branches (12 in branch 0 and 149
in branch 1). Two complete transformed polynomial fixtures are checked in
each represented branch. No valid witness for branches 2 or 3 is assumed;
the symbolic checks cover both branches regardless.

For the previously known six-completion original-color prefix, the predicted
four dimensions remain `[6,0,0,0]`. Original fixes must use the exported
actual-color polynomials. The offset and sign are already retained, so these
predictions and every eventual branch count have multiplier and divisor one.
No solver is run here.

A full count requires exactly one completed certified dimension for each
of the four branch IDs. Reduced/unreduced and natural/minimum-fill models
are alternative presentations of the same branch and must never be added
together. An incomplete branch remains unknown. All earlier inputs and
backend code remain unchanged.
