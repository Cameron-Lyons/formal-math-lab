# Uniform exclusion of positive-slope cubic substitutions at 7

Suppose $X, Y, Z \in \mathbb{Q}[t]$ have degree at most 6 and constant terms $(0, 1, 1)$ or $(-2, 3, 1)$. Set $Q = 1 - Dt^2$ for a nonzero integer $D$. If

$$
X^3 + ZY^2 + Z^2 Q^3 = 2 Q^9,
$$

then every coefficient of $X, Y, Z$ is integral at 7. The same holds for the seeds $(1, 0, 1)$ and $(1, 0, -1)$. In particular, this covers $D = 3$ and closes both positive-slope cases left open by the finite-precision calculations in [cubic_chart_obstructions.md](cubic_chart_obstructions.md).

## The two scales

Suppose some coefficient is not integral at 7. Let $h$ be the maximum of $-v_7(f_i)/i$ over all nonzero coefficients of $X, Y, Z$ with $i > 0$. Then $h$ is a positive rational number. Replace $t$ with $7^h t$, working in a finite totally ramified extension if $h$ is fractional.

After rescaling, all three polynomials have integral coefficients and at least one nonconstant term survives reduction. The denominator becomes $1 - Ct^2$, where $C = D 7^{2h}$ has positive valuation, so the denominator reduces to 1. Reducing modulo the maximal ideal gives an ordinary polynomial solution to $x^3 + zy^2 + z^2 = 2$ over $\mathbb{F}_7$.

[cubic_annulus_residues.py](cubic_annulus_residues.py) enumerates all $7^6$ coefficient vectors for $x$ (including the zero vector) and all allowed divisors $z \mid 2 - x^3$. It finds:

* 6 nonconstant triples at $(0, 1, 1)$,
* 42 nonconstant triples at $(-2, 3, 1)$,
* 18 nonconstant triples at each of $(1, 0, 1)$ and $(1, 0, -1)$.

Every nonconstant triple has $\deg y = 3$ and $\deg z = 6$. The script checks both degree facts directly before normalizing the chart.

The rest of the proof works over any discretely valued field whose residue characteristic is not 2 or 3. Reverse the balanced numerators by setting $A(s) = s^6 X(1/s)$, $B(s) = s^6 Y(1/s)$, and $E(s) = s^6 Z(1/s)$, and write $B_i = [s^i]B(s)$. From the degrees modulo the maximal ideal, $E(0)$ and $B_3$ are units, while any nonzero $B_0, B_1, B_2$ have positive valuation. The reversed equation is

$$
A^3 + EB^2 + E^2(s^2 - C)^3 = 2(s^2 - C)^9.
$$

Define

$$
r = \min\left\{\tfrac{1}{2}v(C),\, v(B_0)/3,\, v(B_1)/2,\, v(B_2)\right\} > 0,
$$

taking $v(0) = +\infty$. In a totally ramified extension, pick $\lambda$ with $v(\lambda) = r$, substitute $s = \lambda T$, and set

$$
A_1 = A(\lambda T)/\lambda^2, \quad B_1^* = B(\lambda T)/\lambda^3, \quad E_1 = E(\lambda T), \quad c_1 = C/\lambda^2.
$$

By construction, $B_1^*$, $E_1$, and $c_1$ are integral. The scaled equation becomes

$$
A_1^3 = 2\lambda^{12}(T^2 - c_1)^9 - E_1(B_1^*)^2 - E_1^2(T^2 - c_1)^3,
$$

so $A_1^3$ is integral as well. This forces $A_1$ to be integral: if $m$ is the least coefficient valuation of a polynomial, then $3m$ is the least coefficient valuation of its cube, because scaling by a uniformizer power gives a nonzero reduction whose cube stays nonzero. [CubicAnnulus.lean](CubicAnnulus.lean) proves this integrality step over any integrally closed ring.

Now let $a, b, e, c$ be the reductions of $A_1, B_1^*, E_1, c_1$. Then $e$ is a nonzero constant and $b = b_0 + b_1 T + b_2 T^2 + b_3 T^3$ with $b_3 \ne 0$. Terms of degree above 3 vanish on reduction because they carry a positive power of $\lambda$. The reduced equation is

$$
a^3 + eb^2 + e^2(T^2 - c)^3 = 0.
$$

By the choice of $r$, either $c \ne 0$ or at least one of $b_0, b_1, b_2$ is nonzero.

## Both reduced equations are impossible

Over a field $k$ of characteristic not 2 or 3 with $e \ne 0$, the equation $x^3 + ey^2 = -e^2$ has only constant solutions in $k(T)$. Clearing reduced denominators turns it into the polynomial Fermat-Catalan equation with exponents $2, 6, 3$, whose positive-characteristic descent is in mathlib and wrapped in [PellConstantFiber.lean](PellConstantFiber.lean).

* If $c = 0$, put $x = a/T^2$ and $y = b/T^3$. The constant-fiber theorem forces $b$ to be a scalar multiple of $T^3$, contradicting the surviving lower coefficient among $b_0, b_1, b_2$.
* If $c \ne 0$, parametrize $d^2 = s^2 - c$ by $s = (w^2 + c)/(2w)$ and $d = (w^2 - c)/(2w)$. Then $x = a(s)/d^2$ and $y = b(s)/d^3$ solve the same constant-fiber equation in $k(w)$, so $b(s) = k_0 d^3$ for some constant $k_0$. Clearing denominators, the coefficient of $w^6$ gives $b_3 = k_0$, while the constant term gives $b_3 c^3 = -k_0 c^3$. Since $c$, $b_3$, and 2 are nonzero, this is a contradiction.

## Verification and trust boundary

The written proof above constructs the fractional-valuation scaling elements and identifies the resulting reduced coefficients. FLINT ([cubic_annulus_residues.py](cubic_annulus_residues.py)) checks the exhaustive finite-field list. Lean verifies the first balancing radius in [PoleTwoReduction.lean](PoleTwoReduction.lean), and checks the second radius, cube integrality, specialization of the scaled identity, and both reduced contradictions in [CubicAnnulus.lean](CubicAnnulus.lean).

```sh
uv run --with python-flint==0.9.0 cubic_annulus_residues.py
lake -d .. build CubicAnnulus
```
