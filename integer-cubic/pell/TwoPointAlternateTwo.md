# The alternate two-point quartic Pell substitution at 2

Suppose $x, y, z$ are rational polynomials on the Pell conic $u^2 - 3v^2 = 1$ of total degrees at most $(4, 3, 6)$ satisfying $x^3 + y^2 z + z^2 = 2$ identically, taking $(0, 1, 1)$ at $(1, 0)$ and $(-2, 3, 1)$ at $(2, 1)$. Because [two_point_alternate_two.lean](two_point_alternate_two.lean) already rules out solutions inside the $2$-integral Pell-coordinate lattice (modulo $4096$), the only remaining loophole is polynomials with arbitrarily high powers of $2$ in their denominators.

This note closes that loophole completely: **every such rational substitution must already lie in the original $2$-integral Pell-coordinate lattice.** Combined with [two_point_alternate_two.lean](two_point_alternate_two.lean), this rules out the pair of marks $(0, 1, 1)$ and $(-2, 3, 1)$ for all rational coefficients.

## Step 1: Coordinate normal form and the slope threshold $h \le 1/2$

As in [TwoPointPrimaryTwo.md](TwoPointPrimaryTwo.md), set $w = u - 1 - v$, so the conic relation becomes
$$
v^2 = (1 + w)v + w + \frac{w^2}{2}.
$$
Each coordinate of degree bound $d$ writes uniquely as $P(w) + v Q(w)$ with $\deg P \le d$ and $\deg Q < d$. Evaluating at the two marks $(w, v) = (0, 0)$ and $(0, 1)$ fixes the constant pairs $(P(0), Q(0))$ for $(x, y, z)$ as $(0, -2)$, $(1, 2)$, and $(1, 0)$, respectively.

Let $h = \max(-v_2(c_i)/i)$ over all nonzero positive-degree coefficients $c_i$ across the six polynomials $P, Q$. If there are no positive-degree coefficients, or if $h \le 1/2$, then rewriting the conic relation as
$$
\frac{w^2}{2} = v^2 - v - (1 + v)w
$$
places every coordinate inside the original $2$-integral Pell-coordinate lattice without raising its degree bound.

## Step 2: Split reductions over $\mathbb{F}_2$ for large slopes ($h > 1/2$)

Now assume for contradiction that $h = a/e > 1/2$ in lowest terms. Rescaling $w$ in a totally ramified extension of $\mathbb{Q}_2$ kills the $w$ terms in the conic relation (reducing it to $v^2 = v$) and splits the reduction into two ordinary polynomial triples over $\mathbb{F}_2[s]$. Because $(-2, 3, 1) \equiv (0, 1, 1) \pmod 2$, both components pass through $(0, 1, 1)$, with at least one surviving nonconstant term and all surviving indices divisible by $e$.

Imposing the degree bounds $\deg P \le d$ and $\deg Q < d$ produces the exact counts below:

| Reduced denominator $e$ | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Nonconstant split residues | 33 | 3 | 1 | 0 | 0 | 0 |

In particular, only $e \in \{1, 2, 3\}$ survive, and the single residue for $e = 3$ is
$$
P = (0,\; 1 + s^3,\; 1 + s^6), \qquad Q = (0,\; 0,\; 0).
$$

## Step 3: Normalized basis and stabilization of mod-4 / mod-8 obstructions

Switch back to $\mathbb{Q}_2$ in the normalized basis $E_i = w^i / 2^{\lfloor hi \rfloor}$, where every coefficient is $2$-integral. [two_point_alternate_balanced_two.py](two_point_alternate_balanced_two.py) enumerates the binary digits of all positive-degree coefficients ($1 \le i \le d$ for $P$, $1 \le i < d$ for $Q$) and tests the $23$ first-correction equations modulo $4$.

Four exceptional parity tuples each yield $1{,}024$ solutions modulo $4$ ($4{,}096$ total), and every one of those is tested modulo $8$ using the same binary Jacobian and the residual divided by $4$:

| Representative slopes | Normalized tuples modulo $2$ per slope | Tuples modulo $4$ per slope | Tuples modulo $8$ |
| --- | ---: | ---: | ---: |
| $1, 2$ | 33 | 0 | 0 |
| $3/2, 5/2$ | 384 | 0 | 0 |
| $4/3, 7/3$ | 512 | 0 | 0 |
| $2/3, 5/3, 8/3, 11/3$ | 512 | 4,096 | 0 |

**Why these 10 representative slopes cover every $h > 1/2$:** Modulo $2^N$ (for $N = 2, 3$), the extra $w, wv, w^2/2$ terms in the multiplication rule for $v^2$ vanish as soon as $h \ge N$. Above that threshold, the remaining multiplication rule depends solely on the fractional part of $h$. Consequently, the mod-$4$ obstructions stabilize at $h \ge 2$, and the mod-$8$ obstruction for fractional part $2/3$ stabilizes at $h \ge 3$. Thus every slope $h > 1/2$ is ruled out.

## Verification, trust boundary, and reproduction

* **Python enumeration and matching:** [two_point_alternate_balanced_two.py](two_point_alternate_balanced_two.py) enumerates all inputs, builds the correction matrices, solves every consistent first step by binary elimination, and matches every terminal matrix to one of **37** certified inconsistent subsystems.
* **Lean certification:** Lean's kernel proves in [TwoPointAlternateTwo.lean](TwoPointAlternateTwo.lean) that all $37$ subsystems are inconsistent for every choice of the $23$ correction digits.
* **Trust boundary:** The $2$-adic balancing argument above and the matching from the Python enumeration to those $37$ certificates lie outside the Lean proof.

After building the Lean project, reproduce both checks with:

```sh
uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
lake -d .. env lean TwoPointAlternateTwo.lean
```
