# Pell families with pole order at most two in x

Suppose a nonsplit Pell conic over $\mathbb{Q}$ has a rational point, and $x, y, z$ are rational functions on it defined over $\mathbb{Q}$ with poles only at the two conjugate points at infinity. Suppose they satisfy $z^2 + y^2 z + x^3 = 2$ identically and take integer values together at one rational point. **If $x$ has pole order at most 2 at infinity, the family is constant.**

The proof combines finite-field enumeration, local lifting, and Lean certificates:

* Lean verifies the pole-order-1 obstruction ([PoleOne.lean](PoleOne.lean)), characteristic-zero constant fibers ([PellConstantFiber.lean](PellConstantFiber.lean)), leading-coefficient and square-factor steps ([PoleTwo.lean](PoleTwo.lean)), polynomial specialization ([PoleTwoReduction.lean](PoleTwoReduction.lean)), uniqueness of nonsingular lifts ([PoleTwoLifting.lean](PoleTwoLifting.lean)), and the even-quadratic obstruction ([SmallCubic.lean](SmallCubic.lean)).
* A C++ program ([pole_two_check.cpp](pole_two_check.cpp)) runs the exhaustive finite-field searches and Jacobian checks.
* The ramified extensions, conic coordinate changes, and positive-characteristic constant-fiber step are written out below.

## The possible pole orders

Every nonconstant $\mathbb{Q}$-rational function regular on the affine conic has poles of equal positive order at its two conjugate ends. Let $K = \mathbb{Q}(\sqrt{D})$ be the splitting field, with $D$ squarefree. Over $K$, the affine coordinate ring is $K[T, T^{-1}]$. Shifting the norm parameter to the marked integer point puts that mark at $T = 1$ with conjugation sending $T \mapsto 1/T$ (this also identifies any nonunit-norm Pell conic having a rational point with the norm-1 conic).

Set $z' = z + y^2$. Every irreducible factor of $z$ over $K$ at a nonzero finite point has degree divisible by 3: at any root of $z$, we have $x^3 = 2$, and $X^3 - 2$ is irreducible over any quadratic number field. If $z$ has pole order $m$, then $T^m z$ has degree $2m$ and nonzero constant term, so $3 \mid m$. The same holds for $z'$.

None of $x, y, z, z'$ can be constant in a nonconstant family:

* If $x$ is constant, then $zz' = 2 - x^3$ is a nonzero constant, so $z$ and $z'$ are Laurent units; conjugation forces any $\mathbb{Q}$-rational Laurent unit to be constant.
* If $z$ is a nonzero rational constant, then $zy^2 = 2 - z^2 - x^3$ is a smooth genus-1 curve (since $z^2 \ne 2$). A nonconstant parametrization would embed its function field inside a rational function field, contradicting Lüroth's theorem. For constant $z'$, apply the same argument to $-z'$.
* If $y$ is constant, putting $w = 2z + y^2$ gives $w^2 = y^4 + 8 - 4x^3$ with $y^4 + 8 \ne 0$, another smooth genus-1 curve.

Therefore the pole orders of $z$ and $z'$ are positive multiples of 3 summing to three times the pole order of $x$. Pole order 1 for $x$ is impossible. Pole order 2 forces pole orders $(3, 3)$ for $(z, z')$, at most 1 for $y$ (since $y^2 = z' - z$), and exactly 3 for $w = 2z + y^2$. From now on, $x, y, w$ have Laurent supports in $[-2, 2]$, $[-1, 1]$, and $[-3, 3]$ with nonzero extreme coefficients.

## Integral coefficients at 13

Work at a place above 13. We use two finite-field results verified by [pole_two_check.cpp](pole_two_check.cpp):

1. Over $\mathbb{F}_{13}$, every polynomial solution of $w^2 = y^4 + 8 - 4x^3$ with $\deg x \le 4$ and $\deg y \le 2$ is constant.
2. Over $\mathbb{F}_{13}$ or $\mathbb{F}_{169}$, every polynomial solution with $\deg x \le 2$ and $\deg y \le 1$ is constant.

Switch to the rational coordinate $s$ defined by $T = (1 + \sqrt{D}\,s)/(1 - \sqrt{D}\,s)$ and put $Q = 1 - Ds^2$. Conjugation invariance turns $(x, y, w)$ into $(X/Q^2, Y/Q, W/Q^3)$ where $X, Y, W \in \mathbb{Q}[s]$ have degrees at most $4, 2, 6$ and integral constant terms at $s = 0$, satisfying

$$
W^2 + 4X^3 = Y^4 Q^2 + 8 Q^6.
$$

Suppose some numerator coefficient has negative valuation (normalized by $v(\pi) = 1$). Let $h = \max(-v(a_i)/i) > 0$ over all nonzero positive-degree numerator coefficients, pick $\lambda$ of valuation $h$ in a totally ramified extension, and substitute $s = \lambda S$. All rescaled coefficients are integral, at least one positive-degree coefficient is a unit, and $Q(\lambda S)$ reduces to 1. Reducing modulo the maximal ideal gives a nonconstant ordinary polynomial solution contradicting result 1. Hence all numerator coefficients are integral.

In [PoleTwoReduction.lean](PoleTwoReduction.lean), `coefficient_balancing_slope` proves that this maximum $h$ is positive, makes all adjusted valuations nonnegative, and attains 0 at a positive index; `specialize_pole_two_at_a_slope` then builds the rescaled polynomials in Mathlib's multiplicative valuation convention and proves the reduced identity, nonconstancy, and degree bounds.

Over the local splitting field, set $s' = \sqrt{D}\,s$, which makes the denominator $1 - s'^2$. If 13 is unramified, $\sqrt{D}$ is a unit and the coefficients in $s'$ stay integral. If 13 ramifies, the residue field is still $\mathbb{F}_{13}$, so the same balancing argument in $s'$ proves integrality again. Finally substitute $s' = (T - 1)/(T + 1)$. Since $1 - s'^2 = 4T/(T + 1)^2$ and 2 is a 13-adic unit, every Laurent coefficient of $x, y, w$ is integral.

These Laurent polynomials also cannot all reduce to constants. If they did, let $h = \min(v(a_i)/i) > 0$ over all nonzero positive-index coefficients, pick $\lambda$ with $v(\lambda) = h$ in a totally ramified extension, and substitute $T = \lambda^{-1} U$. Negative powers drop out on reduction while at least one positive power survives, contradicting result 2. In [PoleTwoReduction.lean](PoleTwoReduction.lean), `specialize_pole_two_towards_infinity` clears the Laurent denominators and proves this specialization step.

In fact, $y$ itself must reduce to a nonconstant Laurent polynomial: for any constant residue $y_0 \in \mathbb{F}_{13}$ or $\mathbb{F}_{169}$, the checker verifies $y_0^4 + 8 \ne 0$, so $w^2 = y_0^4 + 8 - 4x^3$ is smooth of genus 1 and Lüroth's theorem applies (even for inseparable maps). There is also a direct proof using $\delta = T\,d/dT$: on $w^2 = C - 4x^3$ ($C \ne 0$) with nonconstant $x$, we have $w \ne 0$ and $\delta x / w = -\delta w / (6x^2)$. This quotient has no finite nonzero poles (since $x$ and $w$ never vanish together), is regular at any end where $x$ is regular, and vanishes at any end where $x$ has a pole of order $m > 0$ (since $w$ has pole order $3m/2$ while $\delta x$ has pole order at most $m$). Being globally regular with a zero, it vanishes identically, forcing $\delta x = 0$ and hence $x$ constant (since every exponent has absolute value below 13). The same argument covers the ordinary polynomial searches.

## Loss of a pole on reduction

At either end, write $x_2, x_1, \ldots$ and $w_3, w_2, \ldots$ for the leading Laurent coefficients. Comparing orders 6 and 5 gives

$$
w_3^2 = -4x_2^3, \qquad 2w_3 w_2 = -12x_2^2 x_1.
$$

In characteristic zero, $x_2$ and $w_3$ are nonzero. Setting $s = -w_3/(2x_2)$ yields $s^2 = -x_2$, $w_3 = 2s^3$, and $w_2 = -3s x_1$, so $s$ is integral. If $x_2$ vanishes modulo the maximal ideal, then $s, w_3, w_2$ all vanish too, and the order-4 equation forces $y_1^4 = 0$. Therefore, at each end where $y$ keeps its pole on reduction, $x$ must keep its full pole order 2. These are the first two lemmas proved in [PoleTwo.lean](PoleTwo.lean).

## Finite searches

[pole_two_check.cpp](pole_two_check.cpp) works in the standard power basis over $\mathbb{F}_{13}$ and $\mathbb{F}_{169} = \mathbb{F}_{13}[\sqrt{2}]$. It filters candidates by point evaluations, extracts a candidate square root coefficient by coefficient, and verifies hits by direct polynomial multiplication.

For the ordinary searches, normalize nonconstant linear $y$ to $T$ by an affine shift, and over $\mathbb{F}_{13}$, normalize nonconstant quadratic $y$ to $dT^2 + b$ with $d \in \{1, 2\}$ (representing the two nonzero square classes). Test every allowed $x$; constant $y$ is already excluded above.

For the Laurent searches, swap the two ends if needed so $y$ has a pole at $\infty$, and scale $T$ by the unit leading coefficient of $y$ to put

$$
y = T + b + \frac{c}{T}, \qquad X = T^2 x, \qquad Y = Ty, \qquad W = T^3 w,
$$

satisfying $W^2 = T^2 Y^4 + 8T^6 - 4X^3$. Over $\mathbb{F}_{13}$ (which covers both the split and ramified cases), test all $b, c \in \mathbb{F}_{13}$ (including $c = 0$) and all allowed $X$ (here $X_4 \ne 0$, $X_0 = 0$ is allowed only when $c = 0$, and any nonzero extreme coefficient of $X$ must be a square since $-4$ is a square and $w_3^2 = -4x_2^3$).

In the unramified inert case over $\mathbb{F}_{169}$, the outer coefficients of the original $y$ are conjugate, so their product $c$ is a nonzero norm in $\mathbb{F}_{13}$ and $b \in \mathbb{F}_{13}$. In the scaled coordinate, $x_{-j} = c^j \overline{x_j}$, so the program enumerates $x_2, x_1 \in \mathbb{F}_{169}$ and $x_0 \in \mathbb{F}_{13}$. At test points of norm $c$, all three functions take values in $\mathbb{F}_{13}$, so the discriminant must be a square in $\mathbb{F}_{13}$.

| Field and search | Candidate pairs | Square discriminants |
| --- | ---: | ---: |
| Ordinary, 13 elements | 10,024,911 | 0 |
| Ordinary, 169 elements | 4,826,809 | 0 |
| Laurent, 13 elements | 13,537,914 | 6 |
| Laurent with conjugate coefficients, 169 elements | 28,789,488 | 12 |

## Lifting and descent

Every Laurent hit has $c \ne 0$. Holding $c$ fixed leaves 13 unknowns ($b$, the 5 coefficients of $X$, and the 7 of $W$) and 13 coefficient equations. At every hit, the checker verifies that the 13-by-13 Jacobian is invertible (with columns $-4T^3 Y^3$, $12T^i X^2$ for $0 \le i \le 4$, and $2T^i W$ for $0 \le i \le 6$; negating $W$ preserves invertibility and all symmetries).

Hence any two integral lifts with the same exact $c$ and the same reduction must be equal: expressing each equation difference as a row times the vector of input differences produces a matrix reducing to the invertible Jacobian, so its determinant is a unit and its kernel is trivial. Lean proves this general uniqueness theorem in [PoleTwoLifting.lean](PoleTwoLifting.lean).

At every hit, the checker also verifies that the reduced triple is fixed by both involutions

$$
(x(T), y(T), w(T)) \mapsto (x(-T), -y(-T), -w(-T)),
$$
$$
(x(T), y(T), w(T)) \mapsto (x(c/T), y(c/T), -w(c/T)).
$$

Since $c$ is a unit, both operations preserve integrality, the equations, and the exact value of $c$. Lift uniqueness forces both symmetries in characteristic zero, giving $b = 0$ and

$$
y = T + \frac{c}{T}, \qquad
x = A\left(T^2 + \frac{c^2}{T^2}\right) + B = Ay^2 + B - 2Ac, \qquad
w = H\left(T^3 - \frac{c^3}{T^3}\right) + J\left(T - \frac{c}{T}\right),
$$

with $A, H \ne 0$. Evaluating at two rational points on the conic with distinct values of $y^2$ (which exist because the conic is rational and $y$ is nonconstant) shows that $a = A$ and $d = B - 2Ac$ are rational. Using $(T - c/T)^2 = y^2 - 4c$ and $T^3 - c^3/T^3 = (T - c/T)(y^2 - c)$, the surface equation in $s = y^2$ becomes

$$
s^2 + 8 - 4(as + d)^3 = (s - 4c)\bigl(H(s - c) + J\bigr)^2.
$$

This square factor contradicts the existence of the integral triple. `pole_two_square_factor_excluded` in [PoleTwo.lean](PoleTwo.lean) checks this final step, including descending the multiple root to $\mathbb{Q}$.

## Reproduce the finite checks

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror pole_two_check.cpp -o /tmp/pole_two_check
/tmp/pole_two_check
lake -d .. build PoleOne PellConstantFiber PoleTwo PoleTwoReduction PoleTwoLifting
```
