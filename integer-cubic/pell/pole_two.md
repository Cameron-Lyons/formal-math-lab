# Pell families with pole order at most two in $x$

On a nonsplit Pell conic $u^2 - Dv^2 = 1$ (or any norm-$N$ Pell conic having a rational point), every rational function regular on the affine conic can be viewed as a Laurent polynomial in $T = u + \sqrt{D}\,v$ with poles only at the two conjugate points at infinity ($T = 0$ and $T = \infty$). How large must the pole order of $x$ be in a nonconstant family passing through an integer solution of $z^2 + y^2 z + x^3 = 2$?

> **Theorem.** Suppose a nonsplit Pell conic over $\mathbb{Q}$ has a rational point, and $x, y, z$ are $\mathbb{Q}$-rational functions on it with poles only at the two conjugate points at infinity. Suppose they satisfy $z^2 + y^2 z + x^3 = 2$ identically and take integer values together at one rational point. **If $x$ has pole order at most $2$ at infinity, the family is constant.**

## Proof overview and verification architecture

The proof rules out pole order $1$ immediately by degree divisibility, then eliminates pole order $2$ in four stages:

1. **Pinning the pole orders:** Pole order $2$ for $x$ forces pole orders $\le 1$ for $y$ and exactly $3$ for $z$, $z' = z + y^2$, and $w = 2z + y^2$ (solving $w^2 = y^4 + 8 - 4x^3$).
2. **13-adic integrality and nonconstancy:** Balancing at prime $13$ (using two finite-field ordinary-polynomial searches) forces every Laurent coefficient of $x, y, w$ to be integral at $13$, and forces $y$ itself to reduce to a nonconstant Laurent polynomial.
3. **Exhaustive Laurent search at 13:** At any end where $y$ keeps its pole modulo $13$, $x$ must keep its full pole order $2$. Searching all normalized Laurent triples over $\mathbb{F}_{13}$ and $\mathbb{F}_{169}$ finds only $6$ and $12$ hits, respectively.
4. **Hensel rigidity and double symmetry:** Every single hit has $c \ne 0$, an invertible $13 \times 13$ Jacobian, and **two** involutive symmetries. Uniqueness of integral lifts forces both symmetries to hold in characteristic zero, collapsing $x$ to a linear function $x = ay^2 + d$ whose discriminant $s^2 + 8 - 4(as + d)^3$ carries a forbidden square factor!

The verification is split cleanly across three components:

* **Lean 4 proofs:** pole-order-$1$ obstruction ([PoleOne.lean](PoleOne.lean)), characteristic-zero constant fibers ([PellConstantFiber.lean](PellConstantFiber.lean)), leading-coefficient and square-factor steps ([PoleTwo.lean](PoleTwo.lean)), polynomial specialization ([PoleTwoReduction.lean](PoleTwoReduction.lean)), uniqueness of nonsingular lifts ([PoleTwoLifting.lean](PoleTwoLifting.lean)), and the even-quadratic obstruction ([SmallCubic.lean](SmallCubic.lean)).
* **C++23 computation:** [pole_two_check.cpp](pole_two_check.cpp) runs all four exhaustive finite-field searches and checks the $13 \times 13$ Jacobians and involutions at every hit.
* **Written steps (below):** The ramified extensions, conic coordinate changes, and positive-characteristic constant-fiber argument.

## Step 1: The possible pole orders

Every nonconstant $\mathbb{Q}$-rational function regular on the affine conic has poles of equal positive order at its two conjugate ends. Let $K = \mathbb{Q}(\sqrt{D})$ be the splitting field, with $D$ squarefree. Over $K$, the affine coordinate ring is the Laurent polynomial ring $K[T, T^{-1}]$. Shifting the norm parameter to the marked integer point places the mark at $T = 1$, with Galois conjugation acting by $T \mapsto 1/T$. (This same normalization identifies any nonunit-norm Pell conic having a rational point with the norm-$1$ conic.)

Set $z' = z + y^2$, so $zz' = 2 - x^3$.

* **Divisibility by $3$:** Every irreducible factor of $z$ over $K$ at a nonzero finite point has degree divisible by $3$: at any root of $z$, we have $x^3 = 2$, and $X^3 - 2$ remains irreducible over any quadratic number field $K$. If $z$ has pole order $m$, then $T^m z$ is a polynomial of degree $2m$ with nonzero constant term, so $3 \mid 2m$, hence $3 \mid m$. The exact same holds for $z'$.
* **None of $x, y, z, z'$ can be constant in a nonconstant family:**
  * If $x$ is constant, then $zz' = 2 - x^3$ is a nonzero constant, so $z$ and $z'$ are Laurent units $c T^k$; conjugation invariance $T \mapsto 1/T$ forces any $\mathbb{Q}$-rational Laurent unit to be constant.
  * If $z$ is a nonzero rational constant, then $zy^2 = 2 - z^2 - x^3$ is a smooth genus-$1$ curve (since $z^2 \ne 2$ over $\mathbb{Q}$). A nonconstant parametrization would embed its function field inside a rational function field, contradicting Lüroth's theorem. For constant $z'$, apply the same argument to $-z'$.
  * If $y$ is constant, completing the square via $w = 2z + y^2$ gives $w^2 = y^4 + 8 - 4x^3$ with $y^4 + 8 \ne 0$, another smooth genus-$1$ curve.

Therefore, the pole orders of $z$ and $z'$ are **positive multiples of $3$** summing to $3$ times the pole order of $x$:

* **Pole order $1$ for $x$** is immediately impossible (two positive multiples of $3$ cannot sum to $3$).
* **Pole order $2$ for $x$** forces pole orders $(3, 3)$ for $(z, z')$, pole order at most $1$ for $y$ (since $y^2 = z' - z$), and pole order exactly $3$ for $w = 2z + y^2$ (since $w^2 = y^4 + 8 - 4x^3$).

From now on, $x$, $y$, and $w$ are Laurent polynomials supported in $[-2, 2]$, $[-1, 1]$, and $[-3, 3]$ with nonzero extreme coefficients.

## Step 2: Integral coefficients and nonconstant reduction at 13

Work at a place above $13$. We use two ordinary-polynomial finite-field results verified by [pole_two_check.cpp](pole_two_check.cpp):

1. Over $\mathbb{F}_{13}$, every polynomial solution of $w^2 = y^4 + 8 - 4x^3$ with $\deg x \le 4$ and $\deg y \le 2$ is constant.
2. Over $\mathbb{F}_{13}$ or $\mathbb{F}_{169}$, every polynomial solution with $\deg x \le 2$ and $\deg y \le 1$ is constant.

### Why all Laurent coefficients are 13-integral

Switch to the rational parameter $s$ defined by $T = (1 + \sqrt{D}\,s)/(1 - \sqrt{D}\,s)$ and put $Q = 1 - Ds^2$. Conjugation invariance turns $(x, y, w)$ into $(X/Q^2, Y/Q, W/Q^3)$, where $X, Y, W \in \mathbb{Q}[s]$ have degrees at most $4, 2, 6$, have integral constant terms at $s = 0$ (the marked point), and satisfy

$$
W^2 + 4X^3 = Y^4 Q^2 + 8 Q^6.
$$

Suppose some coefficient of $X, Y, W$ has negative valuation (normalized by $v(\pi) = 1$). Let $h = \max_{i>0}(-v(a_i)/i) > 0$ over all nonzero positive-degree numerator coefficients, pick $\lambda$ of valuation $h$ in a totally ramified extension, and substitute $s = \lambda S$. Every rescaled coefficient becomes integral, at least one positive-degree coefficient is a unit, and $Q(\lambda S)$ reduces to $1$. Reducing modulo the maximal ideal gives a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$ contradicting result 1. Hence all numerator coefficients are integral.

In [PoleTwoReduction.lean](PoleTwoReduction.lean), `coefficient_balancing_slope` proves that this maximum $h$ is positive, makes all adjusted valuations nonnegative, and attains $0$ at a positive index; `specialize_pole_two_at_a_slope` builds the rescaled polynomials in Mathlib's multiplicative valuation convention and verifies the reduced identity, nonconstancy, and degree bounds.

Now pass to the local splitting field and set $s' = \sqrt{D}\,s$, turning the denominator into $1 - s'^2$:

* If $13$ is **unramified**, $\sqrt{D}$ is a unit, so coefficients in $s'$ stay integral.
* If $13$ **ramifies**, the residue field is still $\mathbb{F}_{13}$, so repeating the exact same balancing argument in $s'$ proves integrality again.

Finally, substitute $s' = (T - 1)/(T + 1)$. Because $1 - s'^2 = 4T/(T + 1)^2$ and $2$ is a $13$-adic unit, converting back to $T$ preserves integrality: **every Laurent coefficient of $x, y, w$ is integral at $13$**.

### Why $y$ itself reduces to a nonconstant Laurent polynomial

First, the three Laurent polynomials cannot all reduce to constants: if they did, let $h = \min_{i>0}(v(a_i)/i) > 0$ over all nonzero positive-index coefficients, pick $\lambda$ with $v(\lambda) = h$ in a totally ramified extension, and substitute $T = \lambda^{-1} U$. Negative powers drop out on reduction while at least one positive power survives, producing a nonconstant ordinary solution contradicting result 2. In [PoleTwoReduction.lean](PoleTwoReduction.lean), `specialize_pole_two_towards_infinity` clears the Laurent denominators and proves this specialization step.

Moreover, **$y$ itself cannot reduce to a constant $y_0$**: for every $y_0 \in \mathbb{F}_{13}$ or $\mathbb{F}_{169}$, the checker verifies $y_0^4 + 8 \ne 0$, so $w^2 = y_0^4 + 8 - 4x^3$ is smooth of genus $1$ and Lüroth's theorem rules out nonconstant rational maps (even inseparable ones).

There is also a completely elementary proof using the logarithmic derivation $\delta = T\,d/dT$: on $w^2 = C - 4x^3$ ($C \ne 0$) with nonconstant $x$, we have $w \ne 0$ and differentiating gives $2w\,\delta w = -12x^2\,\delta x$, hence

$$
\frac{\delta x}{w} = -\frac{\delta w}{6x^2}.
$$

Inspect the poles and zeros of this rational function on $\mathbb{P}^1$:

* **No finite nonzero poles:** $x$ and $w$ never vanish simultaneously (since $C \ne 0$), so one of the two equivalent denominators is nonzero at every $T \ne 0, \infty$.
* **Regular at every end where $x$ is regular:** $w$ is also regular there, and $\delta x$ stays regular.
* **Vanishes at every end where $x$ has a pole of order $m > 0$:** $w$ has pole order $3m/2$, while $\delta x$ has pole order at most $m < 3m/2$.

A globally regular function on $\mathbb{P}^1$ that vanishes at a point must be identically zero! Thus $\delta x = 0$, forcing $x$ to be constant (since every Laurent exponent has absolute value strictly below $13$). The same argument applies to the ordinary polynomial searches.

## Step 3: Pole retention on reduction

At either end ($T = \infty$ or $T = 0$), write $x_2, x_1, \ldots$ and $w_3, w_2, \ldots$ for the leading Laurent coefficients of $x$ and $w$. Comparing the coefficients of orders $6$ and $5$ in $w^2 = y^4 + 8 - 4x^3$ gives

$$
w_3^2 = -4x_2^3, \qquad 2w_3 w_2 = -12x_2^2 x_1.
$$

In characteristic zero, $x_2$ and $w_3$ are nonzero. Setting $s = -w_3/(2x_2)$ yields

$$
s^2 = -x_2, \qquad w_3 = 2s^3, \qquad w_2 = -3s x_1,
$$

showing $s$ is integral (because $x_2$ is). Now suppose $x_2$ vanishes modulo the maximal ideal: then $s$, $w_3$, and $w_2$ all vanish modulo the maximal ideal as well, and the order-$4$ equation $w_2^2 + 2w_3 w_1 = y_1^4 - 12x_2 x_1^2 - 12x_2^2 x_0$ forces $y_1^4 \equiv 0$.

> **Pole-retention lemma:** At each end where $y$ keeps its pole on reduction, $x$ must keep its full pole order $2$.

These are the first two lemmas proved in [PoleTwo.lean](PoleTwo.lean).

## Step 4: Exhaustive finite searches over $\mathbb{F}_{13}$ and $\mathbb{F}_{169}$

[pole_two_check.cpp](pole_two_check.cpp) works in the standard power basis over $\mathbb{F}_{13}$ and $\mathbb{F}_{169} = \mathbb{F}_{13}[\sqrt{2}]$. It filters candidates rapidly by point evaluations, extracts any candidate square root coefficient by coefficient, and verifies every hit by direct polynomial multiplication.

* **Ordinary searches:** Constant $y$ is already excluded above. Normalize nonconstant linear $y$ to $T$ by an affine shift, and over $\mathbb{F}_{13}$, normalize nonconstant quadratic $y$ to $dT^2 + b$ with $d \in \{1, 2\}$ (the two nonzero square classes). Test every allowed $x$.
* **Laurent searches:** Swap the two ends if needed so $y$ has a pole at $\infty$, and scale $T$ by the unit leading coefficient of $y$ to write

  $$
  y = T + b + \frac{c}{T}, \qquad X = T^2 x, \qquad Y = Ty, \qquad W = T^3 w,
  $$

  satisfying $W^2 = T^2 Y^4 + 8T^6 - 4X^3$.
  * **Over $\mathbb{F}_{13}$ (split and ramified cases):** Test all $b, c \in \mathbb{F}_{13}$ (including $c = 0$) and all allowed $X$ (here $X_4 \ne 0$, $X_0 = 0$ is allowed only when $c = 0$, and any nonzero extreme coefficient of $X$ must be a square because $-4$ is a square mod $13$ and $w_3^2 = -4x_2^3$).
  * **Over $\mathbb{F}_{169}$ (unramified inert case):** The outer coefficients of the original $y$ are Galois conjugates, so their product $c$ is a nonzero norm in $\mathbb{F}_{13}$ and $b \in \mathbb{F}_{13}$. In the scaled coordinate, $x_{-j} = c^j \overline{x_j}$, so the program enumerates $x_2, x_1 \in \mathbb{F}_{169}$ and $x_0 \in \mathbb{F}_{13}$. At test points of norm $c$, all three functions take values in $\mathbb{F}_{13}$, so the discriminant must be a square in $\mathbb{F}_{13}$.

| Field and search | Candidate pairs | Square discriminants |
| --- | ---: | ---: |
| Ordinary, 13 elements | 10,024,911 | 0 |
| Ordinary, 169 elements | 4,826,809 | 0 |
| Laurent, 13 elements | 13,537,914 | 6 |
| Laurent with conjugate coefficients, 169 elements | 28,789,488 | 12 |

## Step 5: Lifting uniqueness, double symmetry, and final contradiction

Every single one of the $6 + 12$ Laurent hits has $c \ne 0$ (meaning $y$ keeps its poles at both ends).

1. **Hensel uniqueness for fixed $c$:** Holding $c$ fixed leaves $13$ unknowns ($b$, the $5$ coefficients of $X$, and the $7$ of $W$) constrained by $13$ coefficient equations. At every hit, the checker verifies that the $13 \times 13$ Jacobian is invertible (with columns $-4T^3 Y^3$, $12T^i X^2$ for $0 \le i \le 4$, and $2T^i W$ for $0 \le i \le 6$; negating $W$ preserves invertibility and all symmetries). Consequently, any two integral lifts sharing the same exact $c$ and the same reduction must be **identical**: factoring each equation difference as a linear combination of input differences produces a matrix reducing to the invertible Jacobian, so its determinant is a unit and its kernel is trivial. Lean proves this general uniqueness theorem in [PoleTwoLifting.lean](PoleTwoLifting.lean).
2. **Two exact involutions forced in characteristic zero:** At every hit, the checker also verifies that the reduced triple is fixed by **both** involutions

   $$
   (x(T), y(T), w(T)) \mapsto (x(-T), -y(-T), -w(-T)),
   $$
   $$
   (x(T), y(T), w(T)) \mapsto (x(c/T), y(c/T), -w(c/T)).
   $$

   Because $c$ is a unit, both operations preserve integrality, the defining equations, and the exact value of $c$. By lift uniqueness, **both symmetries must hold identically in characteristic zero**!
3. **Collapse to a square-factor contradiction:** The two symmetries immediately kill $b$ ($b = 0$) and force the Laurent expansions to take the exact shape

   $$
   y = T + \frac{c}{T}, \qquad
   x = A\left(T^2 + \frac{c^2}{T^2}\right) + B = Ay^2 + B - 2Ac, \qquad
   w = H\left(T^3 - \frac{c^3}{T^3}\right) + J\left(T - \frac{c}{T}\right),
   $$

   with $A, H \ne 0$. Evaluating at two rational points on the conic with distinct values of $y^2$ (which exist because the conic is rational and $y$ is nonconstant) forces $a = A$ and $d = B - 2Ac$ to be rational. Using the identities $(T - c/T)^2 = y^2 - 4c$ and $T^3 - c^3/T^3 = (T - c/T)(y^2 - c)$, the surface equation in $s = y^2$ becomes

   $$
   s^2 + 8 - 4(as + d)^3 = (s - 4c)\bigl(H(s - c) + J\bigr)^2.
   $$

   This repeated factor contradicts the existence of the integral triple! The theorem `pole_two_square_factor_excluded` in [PoleTwo.lean](PoleTwo.lean) certifies this final step in Lean, including descending the multiple root to $\mathbb{Q}$.

## Reproduce the finite checks

```sh
c++ -O3 -std=c++23 -Wall -Wextra -Wpedantic -Werror pole_two_check.cpp -o /tmp/pole_two_check
/tmp/pole_two_check
lake -d .. build PoleOne PellConstantFiber PoleTwo PoleTwoReduction PoleTwoLifting
```
