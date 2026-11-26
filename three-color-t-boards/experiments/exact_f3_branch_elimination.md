# Exact affine elimination of the four linear sign branches

Eliminating the linear equations of the four sign branches shrinks the inputs to **96, 95, 94, and 93 variables** without changing any branch count, while keeping both independent symmetry factors inside each ring. Their quotient dimensions `N0, N1, N2, N3` sum directly to the full labeled count `N` (with multiplier and divisor 1). None of the four unrestricted dimensions is computed here.

## Exact polynomial-ideal reduction

Starting from the four frozen [linear sign branches](exact_f3_sign_branches.md), branch `k` adds `k + 1` affine equations of full rank `k + 1`. Gaussian elimination solves `k + 1` coupled prefix variables as affine forms `L` in the remaining coordinates, never pivoting on the offset `a` or sign `s`. Substituting `L` and projecting back onto the surviving coordinates shows that quotienting by those affine equations gives the exact polynomial ring in the remaining variables.

Over `F₃`, every affine form `L = c + sum(a_i * y_i)` with `c, a_i in F₃` satisfies the ordinary polynomial identity

```
L³ - L = sum_i a_i*(y_i³ - y_i),
```

because `c³ = c` and `a_i³ = a_i` in `F₃`. Every eliminated field equation therefore follows directly from the surviving field equations (checked as ordinary polynomials before any field reduction), so no extra pivot-domain equation or extension-field parameter is needed.

Substituting into the 76 source moments and 4 elementary cubics, then reducing exponents modulo `y_i³ - y_i`, preserves the ideal, and all 80 polynomials stay nonzero. Rebuilding all 80 geometric moments directly in the new affine color coordinates confirms that the 4 unary linear moments vanish identically while the other 76 moments and 4 elementary cubics match term for term.

Each reduced ideal is therefore isomorphic to its original branch ideal. Every remaining variable keeps its field cubic (including `a³ - a` and `s³ - s`), alongside `s² - 1`. Because these split into distinct roots in `F₃`, each quotient is a finite product of copies of `F₃`, so its dimension equals the exact count of labeled boards in that branch without multiplicity.

## Selected affine substitutions

Here `x` indices are **one-based indices in the original 97-variable natural-order input**, not the compacted output indices:

| Branch | Eliminated old variables and replacements |
|---|---|
| 0 | x1=2 |
| 1 | x1=0; x72=1+x16+x71+2*x94 |
| 2 | x1=0; x72=x16+x71+2*x94; x9=2+2*x8+2*x10 |
| 3 | x1=0; x72=x16+x71+2*x94; x9=2*x8+2*x10; x2=2 |

The generator tries every independent coordinate pivot set for each branch (1, 4, 12, and 12 choices) and picks the one minimizing total moment-plus-`e3` term count (breaking ties by largest single-polynomial support, then pivot tuple). That optimizes over coordinate pivot sets only, not arbitrary coordinate changes.

| Branch | Variables | Coupled variables | Generators | Moment terms | e3 terms | Total terms |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 96 | 94 | 177 | 95357 | 566 | 96117 |
| 1 | 95 | 93 | 176 | 97925 | 620 | 98737 |
| 2 | 94 | 92 | 175 | 97832 | 632 | 98654 |
| 3 | 93 | 91 | 174 | 95216 | 602 | 96006 |

Compared to the source's 96,056 coupled terms, elimination trims terms slightly in branches 0 and 3 and increases them slightly in branches 1 and 2. Removing solved variables simplifies the presentation without promising faster basis runs.

## Complete exports, maps, and certificates

The [manifest](exact_f3_branch_elimination_manifest.json) lists all eight files `exact_f3_branch_elimination_k{k}_{natural,minfill}.ms` and their JSON metadata. Each branch has two variable orders: natural order keeps surviving old indices in ascending order, and minimum-fill filters the frozen permutation by removing the same pivots. Offset and sign stay last in both.

Each `.ms` file lists, in order:

1. All surviving field cubics `y_i³ - y_i`.
2. The 76 substituted, field-reduced moments.
3. The 4 substituted, field-reduced elementary cubics.
4. `s² - 1`.

Metadata stores the new-to-old coordinate map, all 97 old coordinates as affine forms in the new variables, all 100 canonical colors as **affine** forms, and all 100 actual colors as polynomials of degree at most 2:

```
z_cell = a + s*d_cell.
```

When `d_cell` has a nonzero constant term, `z_cell` includes a term linear in `s`, so dropping the constant part of `d_cell` would impose wrong prefix constraints. The inverse map still reads `a` from the apex, gets `k` and `s` from the pattern difference, computes `d = s*(z - a)`, takes its Gray prefixes, and projects onto the kept coordinates.

Every source generator gets a recorded image certificate: ordinary affine-domain identities for eliminated domains (with combination coefficients labeled in old-97 indices), new input indices for kept domains, image hashes for all moments and `e3` cubics, and ordinary vanishing identities for the removed branch equations. Nothing is dropped silently.

Natural and minimum-fill exports are checked against each other by inverse polynomial renaming; because both place field cubics in ascending variable order, the audit also records the full generator permutation.

## Checks and counting scope

Run `python experiments/exact_f3_branch_elimination.py --check` to regenerate the [audit](exact_f3_branch_elimination_audit.json), input hashes, pivot comparisons, ordinary identities, and fresh geometric checks. Eight arbitrary assignments per branch verify the coordinate bijections (coordinate tests only, not valid boards); 161 existing valid witnesses round-trip in their true branches (12 in branch 0, 149 in branch 1), with two complete polynomial fixtures checked per populated branch. The symbolic proofs cover branches 2 and 3 even without stored witnesses.

For the known six-completion prefix, the predicted branch dimensions stay `[6, 0, 0, 0]` (using the exported quadratic actual-color polynomials, with multiplier and divisor 1). No solver runs here.

Getting the full unrestricted count still requires one certified unrestricted count for each branch ID `0..3`. Reduced vs. unreduced and natural vs. minimum-fill variants are alternative forms of the same branch and must never be summed together; any unfinished branch stays unknown. Earlier inputs and backend code were left untouched.
