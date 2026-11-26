# The alternate two-point quartic Pell substitution at 2

Suppose $x, y, z$ are rational polynomials on $u^2 - 3v^2 = 1$ of total degrees at most $(4, 3, 6)$ satisfying $x^3 + y^2 z + z^2 = 2$ identically, taking $(0, 1, 1)$ at $(1, 0)$ and $(-2, 3, 1)$ at $(2, 1)$. Every such substitution must lie in the original 2-integral Pell-coordinate lattice. Combined with the separate integral-lattice obstruction in [two_point_alternate_two.lean](two_point_alternate_two.lean), this rules out this pair of marks completely.

As in [TwoPointPrimaryTwo.md](TwoPointPrimaryTwo.md), set $w = u - 1 - v$, so $v^2 = (1 + w)v + w + w^2/2$, and write each coordinate uniquely as $P(w) + vQ(w)$ with $\deg P \le d$ and $\deg Q < d$. The constant pairs $(P(0), Q(0))$ for $(x, y, z)$ are $(0, -2)$, $(1, 2)$, and $(1, 0)$. Let $h = \max(-v_2(c_i)/i)$ over all nonzero positive-degree coefficients $c_i$. If there are no positive-degree coefficients or if $h \le 1/2$, the relation $w^2/2 = v^2 - v - (1 + v)w$ places every coordinate in the original 2-integral lattice.

Now assume $h = a/e > 1/2$ in lowest terms. Rescaling $w$ in a totally ramified extension makes both components of the split reduction ordinary polynomial triples over $\mathbb{F}_2$ passing through $(0, 1, 1)$, with at least one surviving nonconstant term and all surviving indices divisible by $e$. Imposing the degree bounds on $P$ and $Q$ gives the complete counts below:

| Reduced denominator $e$ | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Nonconstant split residues | 33 | 3 | 1 | 0 | 0 | 0 |

The single residue for $e = 3$ is $P = (0, 1 + s^3, 1 + s^6)$, $Q = (0, 0, 0)$. Switching to the normalized basis $E_i = w^i / 2^{\lfloor hi \rfloor}$, [two_point_alternate_balanced_two.py](two_point_alternate_balanced_two.py) enumerates the binary digits of all positive-degree coefficients ($1 \le i \le d$ for $P$, $1 \le i < d$ for $Q$) and tests the 23 first-correction equations. Four exceptional parity tuples each yield 1,024 solutions modulo 4 (4,096 total), and every one of those is tested modulo 8 using the same binary Jacobian and the residual divided by 4:

| Representative slopes | Normalized tuples modulo 2 per slope | Tuples modulo 4 per slope | Tuples modulo 8 |
| --- | ---: | ---: | ---: |
| $1, 2$ | 33 | 0 | 0 |
| $3/2, 5/2$ | 384 | 0 | 0 |
| $4/3, 7/3$ | 512 | 0 | 0 |
| $2/3, 5/3, 8/3, 11/3$ | 512 | 4,096 | 0 |

Modulo $2^N$ (for $N = 2, 3$), the extra $w, wv, w^2/2$ terms in the multiplication rule for $v^2$ vanish as soon as $h \ge N$. Above that threshold, the remaining rule depends only on the fractional part of $h$. Thus the mod-4 obstructions stabilize at $h \ge 2$, and the mod-8 obstruction for fractional part $2/3$ stabilizes at $h \ge 3$. The representative slopes in the table cover every slope $h > 1/2$.

Python ([two_point_alternate_balanced_two.py](two_point_alternate_balanced_two.py)) enumerates the inputs, builds the correction matrices, solves every consistent first step by binary elimination, and matches every terminal matrix to one of 37 certified inconsistent subsystems. Lean's kernel proves in [TwoPointAlternateTwo.lean](TwoPointAlternateTwo.lean) that all 37 subsystems are inconsistent for every choice of the 23 correction digits. The balancing argument above and the matching from the enumeration to those 37 certificates lie outside the Lean proof.

After building the Lean project, reproduce both checks with:

```sh
uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
lake -d .. env lean TwoPointAlternateTwo.lean
```
