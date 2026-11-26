# A quartic Pell substitution through one marked point

Consider the Pell conic $u^2 - 3v^2 = 1$ with the single mark $(x, y, z) = (0, 1, 1)$ at $(u, v) = (1, 0)$ and degree bounds $(4, 3, 6)$. The calculations below resolve several restricted classes over $\mathbb{Q}_2$ and $\mathbb{Q}_3$, while the general mixed quartic remains open over both $\mathbb{Q}_3$ and $\mathbb{Q}$.

## A substitution over the 2-adic field

Over any field of characteristic zero, set

$$
Y(s) = \frac{108s^3 - 239}{13}, \quad
X(s) = \frac{2s(Y(s) - 1)}{3}, \quad
Z(s) = \frac{44 - Y(s)^2 - 16Y(s)}{27}.
$$

These polynomials satisfy $X^3 + Y^2 Z + Z^2 = 2$ identically. Since $3s^3 - 7$ is even at $s = 1$ and its derivative is odd there, Hensel's lemma gives a root $a \in \mathbb{Z}_2$ of $3a^3 = 7$. Setting $s = a + v$ hits the mark $(0, 1, 1)$ at $v = 0$ and satisfies $X(a + 1) \ne 0$. Lean proves the identity, the root in $\mathbb{Z}_2$, and $X(a + 1) \ne 0$ in [OneMarkLocalTwo.lean](OneMarkLocalTwo.lean).

## Two restricted classes over the 3-adic field

Both exclusions in this section are checked in [local_quartic_three.py](local_quartic_three.py).

### Ordinary polynomials of degrees at most $(4, 3, 6)$

There is no nonconstant triple of ordinary polynomials in $\mathbb{Q}_3[t]$ of degrees at most $(4, 3, 6)$ taking the seed $(0, 1, 1)$ at $t = 0$.

To see why, let $h$ be the maximum of $-v_3(c_i)/i$ over all nonzero positive-degree coefficients $c_i$, and rescale $t$ by an element of valuation $h$ in a totally ramified extension. The rescaled polynomials are integral with at least one nonconstant reduction, and every surviving positive index is a multiple of the reduced denominator of $h$. If $X$ reduces to 0, then $Z(Z + Y^2) = 2$ forces $Y$ and $Z$ to be constant, so $X$ must have nonconstant reduction.

There are 26 reduced triples modulo 3. Only 2 are supported on even indices, and none is supported on multiples of any denominator from 3 to 6 (larger denominators cannot occur).

* When $h$ is an integer, 24 of the 26 classes fail modulo 9. Each of the remaining 2 has 177,147 lifts modulo 81, and all of them fail modulo 243.
* When $h$ is a half-integer, first scale by the integer part of $h$, giving the coefficient basis $t^i / 3^{\lfloor i/2 \rfloor}$. Checking the odd-index coefficients in this basis leaves 18 classes modulo 3, and every one has a correction matrix of rank 9 with augmented rank 10.

This also rules out seeded triples of the form $X(\ell), Y(\ell), Z(\ell)$ for any nonconstant linear Pell function $\ell$ and ordinary polynomials of degrees at most $(4, 3, 6)$, simply by shifting $\ell$ to vanish at the mark.

### Quadratic graphs in $y$

The second exclusion rules out $x = A(y - 1)^2 + B(y - 1)$ with $A \ne 0$ over $\mathbb{Q}_3$. Put $s = y - 1$. The double cover

$$
w^2 = F(s) = (1 + s)^4 + 8 - 4(As^2 + Bs)^3
$$

must contain a component parametrized by the Pell conic, so after removing all square factors from $F$, the squarefree part has degree at most 2. Since $\deg F = 6$, we must have $\deg\gcd(F, F') \ge 2$.

Thus the Sylvester matrix of $F$ and $F'$ has corank at least 2, so its determinant and all its first cofactors vanish. Differentiating the determinant with respect to $B$ gives zero as well. Writing $\operatorname{disc}_s(F) = c A^3 D(A, B)$, we get $D = D_B = 0$. The leading coefficient of $D$ in $B$ is $59049 A$. Up to a constant and a power of $A$, $\operatorname{disc}_B(D)$ factors into powers of polynomials of degrees 6, 24, and 48. Their Newton polygons force any 3-adic root to be a unit, and the three factors have no unit root modulo 9, 3, and 81, respectively.

## Integral numerator chart

Set $L = 1 - 3t^2$ and write $(x, y, z) = (X/L^4, Y/L^3, Z/L^6)$. Numerators in $\mathbb{Z}_3[t]$ have degrees at most $(8, 6, 12)$, constant terms $(0, 1, 1)$, and satisfy $X^3 + Z(Y^2 + Z) = 2L^{12}$. The table counts how many residue triples modulo 3 lift to each power of 3:

| Modulus | All surviving residues | Nonconstant reduced $X$ |
| --- | ---: | ---: |
| 3 | 759 | 758 |
| 9 | 21 | 20 |
| 27 | 19 | 18 |
| 81 | 17 | 16 |

The constant residue lifts exactly as $(0, L^3, L^6)$. In the nonconstant classes, we first solve the linear system for $Y$ and $Z$ modulo 9, and then adjust $X$ by multiples of $3^k$ and $Y, Z$ by multiples of $3^{k+1}$ for $k \ge 1$. At order $3^{k+1}$, the equation is linear modulo 3 with columns $X^2 t^i$, $2YZ t^i$, and $(Y^2 + 2Z) t^i$.

In all 21 residues modulo 3 that lift to modulus 9, the top coefficients $a = X_8$, $b = Y_6$, and $c = Z_{12}$ vanish modulo 3. The degree-24 equation then gives $a^3 + b^2 c + c^2 \equiv 0 \pmod{81}$, which forces $a \equiv c \equiv 0 \pmod 9$. This eliminates the 2 classes lost between 27 and 81. [quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py) verifies explicit lifts in every surviving class by direct multiplication, and [OneMarkLocalThree.lean](OneMarkLocalThree.lean) certifies the leading-coefficient implication on integer representatives.

## Integral coefficients in the Pell ring

Write a degree-$d$ Pell function as $P(v) + uQ(v)$ with $P, Q \in \mathbb{Z}_3[v]$, $\deg P \le d$, and $\deg Q < d$. The pair $f_\pm = P \pm Q$ has matching degree-$d$ coefficients, and since 2 is invertible in $\mathbb{Z}_3$, every pair with matching top coefficients arises this way. Modulo 3, the ring splits into the two components $u = +1$ (containing the mark) and $u = -1$. The exact product rule is

$$
(fg)_\pm = f_\pm g_\pm + \frac{3}{4} v^2 (f_+ - f_-)(g_+ - g_-).
$$

Enumerating $Y$ and $Z$ and taking the unique polynomial cube root for $X$ yields 27 marked component triples and 387 unmarked component triples over $\mathbb{F}_3[v]$. Matching their three top coefficients produces 1,161 pairs, of which 56 lift modulo 9:

| Marked component modulo 3 | Pairs lifting to 9 |
| --- | ---: |
| $(0, 1, 1)$ | 20 |
| $(-v^2, 1, 1 + v^3)$ | 18 |
| $(-v^2, 1, 1 - v^3)$ | 18 |

Of the 36 pairs with a nonconstant marked component, 28 lift to modulus 27 and all 28 continue to lift to modulus 81; [quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py) checks the full polynomial identity modulo 81 for each one. For the 20 pairs with constant marked component, the census stops at modulus 9 (a nonconstant 3-adic function can still reduce to a constant).
