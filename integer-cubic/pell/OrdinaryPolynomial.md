# Ordinary polynomial parametrizations through an integral point

Let $x, y, z \in \mathbb{Q}[t]$ satisfy $z^2 + y^2 z + x^3 = 2$ identically. Suppose $\deg x \le 5$ and all three polynomials take integer values at some rational point $t_0$. **Then all three polynomials are constant.** In fact, the proof only needs the three values at $t_0$ to be integral at 13. All finite-field checks below can be reproduced with [ordinary_polynomial_search.py](ordinary_polynomial_search.py).

## Reduction to a nonconstant map over the residue field

Shift $t_0$ to 0. If at least one polynomial is nonconstant, let $h$ be the maximum of $-v_{13}(a_i)/i$ across all nonzero positive-degree coefficients of $x, y, z$. Write $h = r/s$ in lowest terms and adjoin a root $\pi$ of $\pi^s = 13$ to $\mathbb{Q}_{13}$. By Eisenstein's criterion, this extension is totally ramified with residue field $\mathbb{F}_{13}$.

Setting $t = \pi^r u$ makes every coefficient integral and turns at least one positive-degree coefficient into a unit (even when $h \le 0$). Reducing modulo $\pi$ gives a nonconstant solution over $\mathbb{F}_{13}[u]$ with $\deg x \le 5$.

## Possible degrees

Work now in $\mathbb{F}_{13}[t]$ and set $z' = z + y^2$, so $zz' = 2 - x^3$. Because 2 is not a cube in $\mathbb{F}_{13}$, a constant $x$ makes $zz'$ a nonzero constant, forcing $z$, $z'$, and $y$ to be constant as well. For nonconstant $x$, neither $z$ nor $z'$ vanishes identically.

Every irreducible factor of $z$ or $z'$ has degree divisible by 3, since its residue field contains a root of the irreducible cubic $X^3 - 2$. Neither $z$ nor $z'$ can be constant: if $z = z_0 \ne 0$ is constant, then $z_0 y^2 = 2 - z_0^2 - x^3$ defines a smooth genus-1 curve (since 2 is not a square modulo 13 either). A nonconstant polynomial map into that curve would embed its function field inside $\mathbb{F}_{13}(t)$, contradicting Lüroth's theorem. If $z'$ is constant, the same argument applies to $(x, y, -z')$.

Let $d = \deg x$. The degrees of $z$ and $z'$ are positive multiples of 3 summing to $3d$. If those degrees differ, the larger one equals $2 \deg y$ and must be even. Up to swapping $z$ and $z'$, the only allowed degree patterns for $d \le 5$ are:

| $d$ | Degrees of $z, z'$ | Bound on $\deg y$ |
| --- | --- | --- |
| 1 | none | |
| 2 | 3, 3 | $\le 1$ |
| 3 | 3, 6 | $3$ |
| 4 | 6, 6 | $\le 3$ |
| 5 | 3, 12 | $6$ |

## Two independent quartic checks

For $1 \le d \le 4$, we can shift $t$ to remove the $t^{d-1}$ term of $x$, because $13 \nmid d$. Under $t \mapsto at$ ($a \ne 0$) and $x \mapsto \zeta x$ ($\zeta^3 = 1$), the leading coefficient scales by $a^d \zeta$. Keeping one leading coefficient per coset and all lower coefficients gives 1, 26, 169, and 8,788 candidates for $d = 1, 2, 3, 4$, respectively. (Some representatives may still be equivalent; we only need every equivalence class covered.)

We run two independent checks across these candidates:

1. Factor $2 - x^3$ and list every monic divisor where both the divisor and its cofactor have degree at most 6. For each of its 12 nonzero scalar multiples $z$, test whether $(2 - x^3)/z - z$ is a square. This tests 9,776 monic divisors (117,312 multiples) and finds zero solutions.
2. Pair every normalized $x$ with every $y$ of degree at most 3. Point evaluation at all 13 elements of $\mathbb{F}_{13}$ filters the 256,592,024 pairs down to 11,156 where $y^4 + 8 - 4x^3$ might be a polynomial square. Squarefree factorization (including the leading scalar) confirms that none is a square. This check never factors $2 - x^3$ or enumerates $z$.

## Quintic check

For $d = 5$, fifth powers cover all of $\mathbb{F}_{13}^\times$, so scaling and shifting make $x$ monic with zero $t^4$ term. That leaves $13^4$ choices for the lower coefficients. Replacing $z$ by $-z - y^2$ preserves the equation, so we may assume $\deg z = 3$. Then $z$ must be a scalar multiple of an irreducible cubic factor of $2 - x^3$. Testing every cubic factor and every nonzero scalar produces no square for $y^2$.

Degree 6 already has solutions modulo 13. Writing coefficients in ascending order of degree, one example is $x = (5, 5, 2, 5, 2, 0, 1)$, $y = (1, 4, 5, 0, 10)$, and $z = (8, 4, 3, 7, 1, 2, 7, 5, 2, 5)$. Direct multiplication confirms the identity modulo 13.

## Osculating quadratic curves

Any rational point $(c, v)$ on $v^2 = c^4 + 8$ generates an explicit rational polynomial family. The quadratic with second-order contact at $(c, v)$ is

$$
W(y) = v + \frac{2c^3}{v}(y - c) + \left(\frac{3c^2}{v} - \frac{2c^6}{v^3}\right)(y - c)^2.
$$

Set $A = 3c^8 + 48c^4 - 64$ and $B = c^8 - 48c^4 - 192$. The contact identity reads

$$
v^6 \bigl(y^4 + 8 - W(y)^2\bigr) = -8(y - c)^3 (Ay + cB).
$$

Taking $y = (-v^6 t^3/2 - cB)/A$, $x = t(y - c)$, and $z = (W(y) - y^2)/2$ solves $z^2 + y^2 z + x^3 = 2$. Here $A$ is nonzero over $\mathbb{Q}$. Every curve in this family misses even an integral value of $y$ at every rational $t$. [Osculating.lean](Osculating.lean) checks both the polynomial identity and this modulo-13 obstruction directly.

Run the finite checks with:

```sh
uv run --with python-flint==0.9.0 ordinary_polynomial_search.py
```
