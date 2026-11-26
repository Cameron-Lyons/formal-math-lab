# Quintic substitutions with a quadratic in the pole-one coordinate

Let $r$ be a function with simple poles at both ends of a Pell conic, let $R$ be its value at the marked point, and set

$$
a = 2 - R^3, \qquad z = \frac{2 - r^3}{a}, \qquad x = r + qz.
$$

**For $R \in \{0, 1, -1, 2, -2\}$, there is no quintic substitution through $(0, 1, 1)$ where $q$ is a quadratic polynomial in $r$.** The coefficients of $q$ are completely unrestricted, and the obstruction holds over any algebraically closed field of characteristic zero. All exact discriminants and squarefree decompositions below can be reproduced with [quintic_invariant_elimination.py](quintic_invariant_elimination.py).

At the marked point we have $z = 1$ and $x = 0$, so $q(R) = -R$. Write $q = -R + b(r - R) + c(r - R)^2$, with $c \ne 0$ for a quintic, and set $h = 2 - r^3$. The cubic surface equation becomes

$$
F(r) = a^2 y^2 = a^3 - ah - 3a^2 r^2 q - 3arq^2 h - q^3 h^2.
$$

As a map from the smooth projective conic to $\mathbb{P}^1$, $r$ has degree 2 and therefore only two geometric branch points by Riemann-Hurwitz. Since the pullback of $F(r)$ to the conic is a square, every odd-multiplicity root of $F$ must be a branch value, so $F$ has at most two odd-multiplicity roots. Because $F$ has degree 12 (with leading coefficient $-c^3$), each odd root uses at least degree 1 and each even root uses at least degree 2, giving at most 7 distinct roots in total and hence $\deg\gcd(F, F') \ge 5$.

In any one-parameter family of polynomials of fixed degree whose leading coefficient stays a unit at a specialized parameter value, the discriminant vanishes there to order at least $\deg\gcd(F, F')$. This follows directly from the Sylvester determinant: its corank equals $\deg\gcd(F, F')$, any determinant of corank $d$ vanishes to order at least $d$, and passing from resultant to discriminant divides by a unit.

Apply this first in the parameter $c$ at fixed $b$. At any solution, $\operatorname{disc}_r(F)$ vanishes to order at least 5 in $c$. Dividing $\operatorname{disc}_r(F)$ by a nonzero integer and $c^{18}$ gives a polynomial $D(b, c)$ with the same vanishing orders at $c \ne 0$. When $R = 0$, $D$ is a polynomial in $C = c^3$, and substituting $c \mapsto c^3$ also preserves multiplicities at $c \ne 0$. Write $v = C$ for $R = 0$ and $v = c$ for the other four values of $R$.

In all five cases, the leading coefficient of $D$ in $v$ is a nonzero integer independent of $b$, so its degree in $v$ never drops. A root of multiplicity at least 5 in $v$ gives $\deg\gcd(D, D_v) \ge 4$. Applying the same Sylvester argument a second time shows that $b$ must be a root of multiplicity at least 4 in $\operatorname{disc}_v(D)$:

| $R$ | Degree in $b$ of the second discriminant | Squarefree blocks as (degree, multiplicity) |
| --- | ---: | --- |
| $0$ | 252 | $(1, 9), (15, 3), (99, 2)$ |
| $1, -1, 2, -2$ | 816 | $(1, 18), (48, 3), (327, 2)$ |

In every case, the only block of multiplicity at least 4 is the degree-1 block, which is $b$ itself, forcing $b = 0$. After removing its power of $v$, the specialization $D(0, v)$ is squarefree, so no $v \ne 0$ can have multiplicity at least 5. This rules out the quintic substitution for all five values of $R$.

```sh
uv run --with python-flint==0.9.0 python quintic_invariant_elimination.py
```
