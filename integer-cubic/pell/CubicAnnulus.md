# Uniform exclusion of positive-slope cubic substitutions at 7

When searching for a degree-3 polynomial map from a Pell conic $u^2 - Dv^2 = 1$ onto the cubic surface $x^3 + y^2 z + z^2 = 2$, clearing denominators in the rational parameter $t$ turns the coordinates into degree-6 numerators $(X, Y, Z) \in \mathbb{Q}[t]^3$ over powers of $Q = 1 - Dt^2$:

$$
X^3 + ZY^2 + Z^2 Q^3 = 2 Q^9.
$$

A natural worry when testing this system modulo $7$ is that rational solutions might hide behind large powers of $7$ in their denominators (a **positive balancing slope** at $7$). This note proves that **cannot happen** for any nonzero integer $D$ and any of the four integer seeds $(0, 1, 1)$, $(-2, 3, 1)$, $(1, 0, 1)$, or $(1, 0, -1)$:

> **Theorem.** Suppose $X, Y, Z \in \mathbb{Q}[t]$ have degree at most $6$, constant terms $(0, 1, 1)$, $(-2, 3, 1)$, $(1, 0, 1)$, or $(1, 0, -1)$, and satisfy $X^3 + ZY^2 + Z^2 Q^3 = 2 Q^9$ for $Q = 1 - Dt^2$ ($D \in \mathbb{Z} \setminus \{0\}$). Then every coefficient of $X, Y, Z$ is **integral at $7$** (no factor of $7$ appears in any denominator).

In particular, this covers $D = 3$ and uniformly closes both positive-slope cases left open by the finite-precision calculations in [cubic_chart_obstructions.md](cubic_chart_obstructions.md).

## Proof strategy: zooming at two radii

Suppose for contradiction that some coefficient of $X, Y, Z$ has a factor of $7$ in its denominator. The proof works by zooming in on the parameter $t$ at **two nested $7$-adic scales** (forming an annulus around the poles of $Q$):

1. **First scale (near the seed $t = 0$):** Rescale $t \mapsto 7^h t$ at the steepest negative-valuation slope $h > 0$. This clears all denominators while keeping at least one nonconstant coefficient nonzero modulo $7$, and turns $Q$ into $1 - Ct^2$ with $v_7(C) = 2h > 0$, so $Q \equiv 1 \pmod 7$. An exhaustive search over $\mathbb{F}_7$ shows that **every** nonconstant mod-$7$ solution has $\deg \bar Y = 3$ and $\deg \bar Z = 6$ — meaning the top three terms of $Y$ vanish modulo $7$, while the top term of $Z$ stays a unit.
2. **Second scale (reversing to $s = 1/t$):** Reversing the degree-6 polynomials turns those small top terms of $Y$ into small low-degree terms $B_0, B_1, B_2$ of $B(s) = s^6 Y(1/s)$. Zooming in around $s = 0$ by a second positive valuation $r > 0$ kills the inhomogeneous term $2(s^2 - C)^9$ upon reduction and leaves a **homogeneous genus-1 fiber equation** $a^3 + eb^2 + e^2(T^2 - c)^3 = 0$ with $e \ne 0$.
3. **Constant-fiber contradiction:** In characteristic $\ne 2, 3$, the smooth elliptic curve $x^3 + ey^2 = -e^2$ has no nonconstant rational-function points (`PellConstantFiber.lean`). Whether $c = 0$ or $c \ne 0$, this forces a contradiction with the surviving low-degree term or nonzero $c$ guaranteed by the choice of $r$.

### Notation summary

| Symbol | Meaning |
| --- | --- |
| $Q = 1 - Dt^2$ | Pell denominator ($D \in \mathbb{Z} \setminus \{0\}$) |
| $h > 0$ | First balancing slope: $\max_{i>0} (-v_7(f_i)/i)$ over nonzero coefficients of $X, Y, Z$ |
| $C = D 7^{2h}$ | Rescaled denominator coefficient (has positive valuation) |
| $A, B, E$ | Reversed degree-6 numerators in $s = 1/t$: $s^6 X(1/s), s^6 Y(1/s), s^6 Z(1/s)$ |
| $B_i = [s^i]B(s)$ | Coefficient of $s^i$ in $B(s)$ ($B_3$ is a unit; $B_0, B_1, B_2$ have positive valuation) |
| $r > 0, \lambda$ | Second scale $r = \min\{\tfrac{1}{2}v(C), v(B_0)/3, v(B_1)/2, v(B_2)\}$ and element with $v(\lambda) = r$ |
| $A_1, B_1^*, E_1, c_1$ | Rescaled objects at $s = \lambda T$; their reductions modulo the maximal ideal are $a, b, e, c$ |

## Scale 1: Balancing near the seed and mod-7 enumeration

Assume some coefficient of $X, Y, Z$ is not integral at $7$. Let $h$ be the maximum of $-v_7(f_i)/i$ over all nonzero coefficients $f_i$ of $X, Y, Z$ with $i > 0$. Since the constant terms are integers and some positive-degree coefficient has negative valuation, $h$ is a positive rational number.

Replace $t$ with $7^h t$, working in a finite totally ramified extension if $h$ is fractional (so the residue field stays $\mathbb{F}_7$). After this rescaling:

* Every coefficient of $X, Y, Z$ is integral, and at least one positive-degree coefficient is a unit (surviving reduction).
* The denominator becomes $1 - Ct^2$, where $C = D 7^{2h}$ has positive valuation, so the denominator reduces to $1$.

Reducing modulo the maximal ideal therefore produces a nonconstant **ordinary polynomial solution** to $x^3 + zy^2 + z^2 = 2$ over $\mathbb{F}_7$ with $\deg x, \deg y, \deg z \le 6$ and the given constant terms.

The script [cubic_annulus_residues.py](cubic_annulus_residues.py) exhaustively enumerates all $7^6$ coefficient vectors for $x$ (including the zero vector) and all allowed divisors $z \mid 2 - x^3$. It finds:

* $6$ nonconstant triples at $(0, 1, 1)$,
* $42$ nonconstant triples at $(-2, 3, 1)$,
* $18$ nonconstant triples at each of $(1, 0, 1)$ and $(1, 0, -1)$.

Crucially, **every** nonconstant triple satisfies $\deg y = 3$ and $\deg z = 6$. The script checks both degree facts directly before normalizing the chart.

## Scale 2: Reversing the polynomials and zooming into the annulus

From this point onward, the argument works over any discretely valued field whose residue field $k$ does not have characteristic $2$ or $3$.

Reverse the balanced degree-6 numerators by setting

$$
A(s) = s^6 X(1/s), \qquad B(s) = s^6 Y(1/s), \qquad E(s) = s^6 Z(1/s),
$$

and write $B_i = [s^i]B(s)$. Translating the degree facts $\deg \bar Y = 3$ and $\deg \bar Z = 6$ into the reversed variable $s$ tells us that:

* $E(0)$ and $B_3$ are units, whereas
* any nonzero $B_0, B_1, B_2$ have strictly positive valuation (because they came from the vanishing $t^6, t^5, t^4$ terms of $Y$).

Multiplying the balanced surface equation by $s^{18}$ gives the reversed identity:

$$
A^3 + EB^2 + E^2(s^2 - C)^3 = 2(s^2 - C)^9.
$$

Now define the second balancing radius (taking $v(0) = +\infty$):

$$
r = \min\left\{\tfrac{1}{2}v(C),\, \frac{v(B_0)}{3},\, \frac{v(B_1)}{2},\, v(B_2)\right\} > 0.
$$

Since $C \ne 0$, we have $r < +\infty$. Passing to a totally ramified extension if necessary, pick $\lambda$ with $v(\lambda) = r$, substitute $s = \lambda T$, and normalize each term by the exact power of $\lambda$ that balances the left-hand side at order $\lambda^6$:

$$
A_1 = \frac{A(\lambda T)}{\lambda^2}, \qquad
B_1^* = \frac{B(\lambda T)}{\lambda^3}, \qquad
E_1 = E(\lambda T), \qquad
c_1 = \frac{C}{\lambda^2}.
$$

Check the integrality of each piece:

* **$B_1^*$, $E_1$, and $c_1$ are integral** directly from the definition of $r$: for $B_1^*(T) = \sum_{i=0}^6 B_i \lambda^{i-3} T^i$, the coefficients for $i = 0, 1, 2$ have valuation $v(B_i) + (i - 3)r \ge 0$, the $T^3$ coefficient is the unit $B_3$, and every term with $i > 3$ carries a strictly positive power $\lambda^{i-3}$.
* **$A_1$ is integral too:** Dividing the reversed equation by $\lambda^6$ isolates $A_1^3$:

$$
A_1^3 = 2\lambda^{12}(T^2 - c_1)^9 - E_1(B_1^*)^2 - E_1^2(T^2 - c_1)^3.
$$

Since the right-hand side is integral, $A_1^3$ is integral. This forces $A_1$ itself to be integral: if $m$ is the least coefficient valuation of a polynomial, then $3m$ is the least coefficient valuation of its cube (scaling by a uniformizer power gives a nonzero reduction over the residue field, whose cube remains nonzero). [CubicAnnulus.lean](CubicAnnulus.lean) proves this cube-integrality step over any integrally closed ring.

Now let $a, b, e, c \in k[T]$ (with $e, c \in k$) be the reductions of $A_1, B_1^*, E_1, c_1$ modulo the maximal ideal:

* $e = \overline{E(0)}$ is a nonzero constant.
* $b = b_0 + b_1 T + b_2 T^2 + b_3 T^3$ with $b_3 = \overline{B_3} \ne 0$ (all terms of degree $> 3$ vanish on reduction because they carry a positive power of $\lambda$).
* The inhomogeneous term $2\lambda^{12}(T^2 - c_1)^9$ vanishes because $v(\lambda^{12}) = 12r > 0$, leaving the homogeneous reduced equation:

$$
a^3 + eb^2 + e^2(T^2 - c)^3 = 0.
$$

Finally, because $r$ was defined as the minimum of $\tfrac{1}{2}v(C), v(B_0)/3, v(B_1)/2, v(B_2)$, at least one entry attains $r$, which guarantees that **either $c \ne 0$ or at least one of $b_0, b_1, b_2$ is nonzero**.

## Both reduced equations are impossible

Over any field $k$ of characteristic not $2$ or $3$ with $e \ne 0$, the smooth genus-1 curve

$$
x^3 + ey^2 = -e^2
$$

has only **constant** solutions in the rational function field $k(T)$. Clearing reduced denominators turns this into the polynomial Fermat–Catalan equation with exponents $(2, 6, 3)$, whose positive-characteristic descent is in mathlib and wrapped in [PellConstantFiber.lean](PellConstantFiber.lean). Both cases for $c$ now collapse:

* **Case 1 ($c = 0$):** Divide the reduced equation by $T^6$ and put $x = a/T^2$, $y = b/T^3$. They satisfy $x^3 + ey^2 = -e^2$ in $k(T)$. The constant-fiber theorem forces $y$ to be a constant, so $b$ must be a scalar multiple of $T^3$. That contradicts the surviving lower coefficient among $b_0, b_1, b_2$.
* **Case 2 ($c \ne 0$):** Parametrize the conic $d^2 = s^2 - c$ rationally by

  $$
  s = \frac{w^2 + c}{2w}, \qquad d = \frac{w^2 - c}{2w}.
  $$

  Setting $x = a(s)/d^2$ and $y = b(s)/d^3$ solves the exact same constant-fiber equation $x^3 + ey^2 = -e^2$ in $k(w)$, so $b(s) = k_0 d^3$ for some constant $k_0 \in k$. Clearing denominators by multiplying by $(2w)^3$, we compare the $w^6$ and $w^0$ coefficients on both sides of $b_3(w^2 + c)^3 + 2wb_2(w^2 + c)^2 + \dots = k_0(w^2 - c)^3$:
  * the coefficient of $w^6$ gives $b_3 = k_0$, while
  * the constant term ($w^0$) gives $b_3 c^3 = -k_0 c^3$.

  Since $c$, $b_3$, and $2$ are all nonzero in $k$, this gives $2b_3 c^3 = 0$, a contradiction.

Thus no coefficient of $X, Y, Z$ can have negative $7$-adic valuation.

## Verification and trust boundary

* **Written proof (above):** Constructs the fractional-valuation scaling elements $\lambda$ in totally ramified extensions and identifies the reduced coefficients at both scales.
* **FLINT computation:** [cubic_annulus_residues.py](cubic_annulus_residues.py) checks the exhaustive finite-field list over $\mathbb{F}_7$ and verifies $\deg y = 3, \deg z = 6$ for every nonconstant solution.
* **Lean 4 proofs:** [PoleTwoReduction.lean](PoleTwoReduction.lean) verifies the first balancing radius, and [CubicAnnulus.lean](CubicAnnulus.lean) verifies the second radius, cube integrality, specialization of the scaled identity, and both reduced contradictions (building on [PellConstantFiber.lean](PellConstantFiber.lean)).

```sh
uv run --with python-flint==0.9.0 cubic_annulus_residues.py
lake -d .. build CubicAnnulus
```
