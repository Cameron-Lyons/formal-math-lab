# A quartic Pell substitution through the seed cannot have an odd integral second abscissa

Suppose a rational polynomial substitution $(x, y, z)$ on the Pell conic $u^2 - 3v^2 = 1$ has coordinate degrees at most $(4, 3, 6)$, maps $(1, 0)$ to $(0, 1, 1)$, and satisfies $x^3 + y^2 z + z^2 = 2$ identically. **If all three coordinates at $(2, 1)$ are integral at $2$, then $x(2, 1)$ must be even.**

This rules out the candidate second point $(1, 0, -1)$—as well as every other $2$-integral point with an odd $x$-coordinate—with **no restriction** on powers of $2$ in the coefficient denominators.

## Step 1: Coordinate normal form and allowed mod-4 targets

Set $w = u - 1 - v$, which vanishes at both marked points ($v = 0$ at $(1, 0)$ and $v = 1$ at $(2, 1)$). The conic equation becomes
$$
v^2 = (1 + w)v + w + \frac{w^2}{2}.
$$
Each coordinate of degree at most $d$ writes uniquely as $P(w) + v Q(w)$ with $\deg P \le d$ and $\deg Q < d$: repeated elimination of $v^2$ preserves the degree bound, and division by the monic quadratic in $v$ guarantees uniqueness. Marked values $c$ at $(1, 0)$ and $b$ at $(2, 1)$ fix the constant terms $P(0) = c$ and $Q(0) = b - c$.

Testing the cubic surface equation $x^3 + y^2 z + z^2 \equiv 2 \pmod 4$ with odd $x$ leaves only **four** possible mod-$4$ target triples at $(2, 1)$:
$$
(1, 0, 1), \qquad (1, 0, 3), \qquad (1, 2, 1), \qquad (1, 2, 3).
$$
All four give the same system modulo $2$, and we test each of the four sets of constants modulo $4$.

## Step 2: Balancing denominators at both marks

Let $h = \max(-v_2(c_i)/i)$ over all nonzero positive-degree coefficients $c_i$ across the six polynomials $P, Q$.

### Case 1: Small slopes ($h \le 1/2$, or all constant)

If there are no positive-degree coefficients, or if $h \le 1/2$, then every index-$i$ denominator divides $2^{\lfloor i/2 \rfloor}$ up to a $2$-adic unit. Using
$$
\frac{w^2}{2} = v^2 - v - (1 + v)w,
$$
every coordinate falls inside the original $2$-integral Pell-coordinate lattice without raising its degree bound. The mod-$4$ integral-lattice check in [QuarticGeometry.md](QuarticGeometry.md#integral-coefficients-in-the-original-pell-coordinates-at-2) (computed by [quartic_local_geometry.py](quartic_local_geometry.py)) forces $x$ to be **even** at every integral Pell point—contradicting the odd second abscissa.

### Case 2: Large slopes ($h = a/e > 1/2$ in lowest terms)

Set $w = \pi^a s$ where $\pi^e = 2$. By Eisenstein's criterion, this extension of $\mathbb{Q}_2$ is totally ramified with residue field $\mathbb{F}_2$.

1. All six rescaled polynomials become integral, at least one positive-degree coefficient is a unit, and any unit at index $i$ requires $e \mid i$ (so $e \le 6$).
2. Because $a > 0$ and $2a - e > 0$, all $w$-terms vanish modulo $\pi$, reducing the conic relation to $v^2 = v$.
3. Evaluating at $v = 0$ and $v = 1$ yields two ordinary polynomial triples $A = P$ and $B = P + Q$ solving the cubic identity over $\mathbb{F}_2[s]$ with the two marked constant terms, component degrees at most $(4, 3, 6)$, strictly smaller component degrees for $Q = B - A$, and at least one nonconstant component.

Exhausting these small spaces over $\mathbb{F}_2[s]$ leaves only $e \in \{1, 2\}$:

| Reduced denominator $e$ | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Split residues | 22 | 1 | 0 | 0 | 0 | 0 |

## Step 3: Testing the first correction modulo 4

Return to $\mathbb{Q}_2$ and switch to the normalized basis $E_i = w^i / 2^{\lfloor hi \rfloor}$, in which every coefficient is $2$-integral:

* Multiplying $E_i E_j$ introduces the factor $2^{\lfloor h(i + j) \rfloor - \lfloor hi \rfloor - \lfloor hj \rfloor}$, which depends only on the fractional part of $h$.
* In $E_i E_j v^2$, the $w$ and $wv$ terms gain a factor of at least $2^{\lfloor h \rfloor}$, while the $w^2/2$ term gains at least $2^{\lfloor 2h \rfloor - 1}$.
* Once $h \ge 2$, all three extra terms vanish modulo $4$.

Thus **only four representative slope cases remain**, and the counts below hold identically for each of the four allowed mod-$4$ target residues:

| Slopes $h$ | Compatible normalized tuples modulo $2$ | Tuples lifting modulo $4$ |
| --- | ---: | ---: |
| $1$ | 22 | 0 |
| Integers $\ge 2$ | 22 | 0 |
| $3/2$ | 256 | 0 |
| Strict half-integers $\ge 5/2$ | 256 | 0 |

For each half-integral slope, the $13$ odd-index coefficients have arbitrary parity before checking the identity, so the script tests all $2^{13} = 8{,}192$ assignments. At every valid mod-$2$ tuple, there are $23$ correction variables (all positive-degree coefficients of $P$ and $Q$ under the degree bounds $4, 3, 6$) and $23$ nonconstant coefficient equations across the two components (degrees at most $12$ and $11$; the constant terms already match modulo $4$). The first-correction linear system is built from the partial derivatives $3x^2$, $2yz$, $y^2 + 2z$ and the residual divided by $2$ (whose sign is irrelevant modulo $2$).

## Verification, trust boundary, and reproduction

* **Python enumeration:** [two_point_primary_two.py](two_point_primary_two.py) enumerates all residue classes, builds all **2,224** correction matrices ($4 \times (22 + 22 + 256 + 256)$), checks their ranks, and matches every matrix to one of **26** inconsistent row subsystems.
* **Lean certification:** Lean's kernel certifies in [TwoPointPrimaryTwo.lean](TwoPointPrimaryTwo.lean) that all $26$ subsystems are inconsistent for every choice of the $23$ correction digits.
* **Trust boundary:** The $2$-adic balancing proof above and the matching from the Python enumeration to the $26$ matrices lie outside the Lean theorem.

Reproduce both checks from this directory:

```sh
uv run --with python-flint==0.9.0 python two_point_primary_two.py
lake -d .. env lean TwoPointPrimaryTwo.lean
```
