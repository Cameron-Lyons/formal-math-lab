# Quartic Pell substitutions through one integer point

On the Pell conic $u^2 - 3v^2 = 1$, use the rational parameter $t$ with $L = 1 - 3t^2$, $u = (1 + 3t^2)/L$, and $v = 2t/L$. We look for a quartic substitution through $(0, 1, 1)$ at $t = 0$:

$$
(x, y, z) = \left(\frac{X}{L^4}, \frac{Y}{L^3}, \frac{Z}{L^6}\right), \qquad X^3 + ZY^2 + Z^2 = 2 L^{12}.
$$

Here $X, Y, Z \in \mathbb{Q}[t]$ have degrees at most $8, 6, 12$, constant terms $0, 1, 1$, and $X \ne 0$. In [MixedPellAmplification.lean](MixedPellAmplification.lean), Lean proves that **any** such identity generates infinitely many integer solutions (and the same holds for any integral seed with nonconstant $x$). The proof picks a subsequence of powers of $2 + \sqrt{3}$ that clears the coefficient denominators while keeping the seed congruence modulo those denominators.

## Descent from the singular residues at 7

Assume the coefficients are integral at 7 and $\gcd(\bar X, \bar L) = 1$ modulo 7. Of the 66 valid triples modulo 7, 48 have Jacobian rank 20, and exactly 4,410 triples modulo 49 over those 48 classes lift to modulus 343. **Of those 4,410 classes, 2,352 cannot come from a rational identity of any coefficient height.**

The modular counts and ranks are exact FLINT calculations in [quartic_first_lifts.py](quartic_first_lifts.py) and [quartic_free_mark.py](quartic_free_mark.py), while Lean checks the characteristic-zero descent in [QuarticPullbackDescent.lean](QuarticPullbackDescent.lean).

To describe the 2,352 excluded classes, set $S = (ct + dt^2)/L$ and consider the sparse composition

$$
x = 3S^4 + bS, \qquad y = 1 + C S^3, \qquad z = 1 + F S^3 + E S^6.
$$

For nonconstant $S$, the cubic surface identity is equivalent to four equations in $b, C, F, E$:

$$
\begin{aligned}
b^3 + 2C + 3F &= 0, \\
3E + (F + C)^2 + 9b^2 &= 0, \\
2(F + C)E + C^2 F + 27b &= 0, \\
E^2 + C^2 E + 27 &= 0.
\end{aligned}
$$

At $(b, C, F, E) \equiv (0, 3, -2, 2) \pmod 7$, the Jacobian of these four equations is invertible. Hensel lifting produces a unique solution in $\mathbb{Z}_7$, equal to $(14, 38, 40, 30) \pmod{49}$; in particular $bC \ne 0$. Up to $t \mapsto -t$ and multiplying $x$ by a cube root of unity, every rank-20 residue modulo 7 comes from one of these compositions. For each choice of $(c, d) \bmod 7$, its 49 lifts modulo 49 produce 49 distinct triples, giving $48 \cdot 49 = 2{,}352$ classes in total.

Next we show that **every** exact $\mathbb{Z}_7$-solution reducing to one of these 2,352 mod-49 classes must be one of these sparse compositions:

* Pick two distinguishing coefficients of $Y$: use $(Y_3, Y_4)$ when $c \not\equiv 0 \pmod 7$ (with variable parts $Cc^3, 3Cc^2 d$), or $(Y_5, Y_6)$ when $c \equiv 0 \pmod 7$ (with variable parts $3Ccd^2, Cd^3$ and $d \not\equiv 0 \pmod 7$). In both cases the Jacobian with respect to $(c, d)$ is invertible modulo 7, so we can tune $(c, d)$ so the sparse composition matches those two coefficients of any exact lift. Because those two coordinates separate the 49 compositions modulo 49, all remaining coefficients also agree modulo 49.
* Hold those two coefficients fixed and let $M$ be the Jacobian in the remaining 24 unknowns. In every listed mod-49 class, $M$ has rank 20 modulo 7 and $v_7(\det M) = 4$, so $7M^{-1}$ has entries in $\mathbb{Z}_7$. Changing $M$ by a multiple of 49 keeps this property because $M^{-1}(M' - M)$ is divisible by 7. If two solutions with the same fixed coordinates differ by a vector $\Delta$ divisible by $7^k$ ($k \ge 2$), Taylor expansion gives $M\Delta \in 7^{2k}\mathbb{Z}_7^{24}$, hence $\Delta \in 7^{2k-1}\mathbb{Z}_7^{24}$. Repeating this step forces $\Delta = 0$.

Now suppose the chart has rational coefficients. Pick two rational values of $t$ where $r = y - 1$ takes distinct nonzero rational values. The matching values of $z$ are rational and satisfy

$$
z - 1 = \frac{F}{C} r + \frac{E}{C^2} r^2,
$$

which forces $k = F/C$ and $\ell = E/C^2$ to be rational. Then $g = b^3/C = -2 - 3k$ is rational and nonzero. Setting $T = bS$ turns the sparse composition into a rational identity:

$$
x = T - \frac{3\ell + (k + 1)^2}{3g^2} T^4, \quad
y = 1 + \frac{T^3}{g}, \quad
z = 1 + \frac{k}{g} T^3 + \frac{\ell}{g^2} T^6.
$$

The same calculation works after twisting $x$ by a cube root of unity, using the new linear coefficient to define $T$. Lean verifies in [QuarticPullbackDescent.lean](QuarticPullbackDescent.lean) that these coefficient equations contradict the rational sparse-quartic obstruction in [QuarticSparse.lean](QuarticSparse.lean). The remaining 2,058 singular mod-49 classes and 18 rank-24 classes modulo 7 are not covered by this descent.

### Consequence when $x$ depends only on $u$

Suppose $D$ is a 7-adic unit with nonsquare residue modulo 7, and consider $u^2 - Dv^2 = 1$ with $L_D = 1 - Dt^2$ and the seed $(0, 1, 1)$. If the chart coefficients are integral at 7 and both poles of $x$ keep order 4 modulo 7, then $x$ cannot be a polynomial in $u$ alone.

Since $D/3$ is a square in $\mathbb{Z}_7^\times$, rescaling $t$ by $\sqrt{D/3}$ identifies the charts at 7 and preserves evenness of $X$. Among the 12 residue orbits modulo 7, only the singular representatives $(c, d) = (0, 1), (0, 6), (1, 0)$ have even $X \bmod 7$. In the first two, every lift is a sparse composition. In the third, all 49 non-composition classes have $X_1 \equiv 14 \pmod{49}$ before symmetry, and twisting or reflecting keeps $X_1 \ne 0$. Thus an even $X$ is forced into a sparse composition, and the descent only needs two rational evaluations of the original $y$ and $z$, so it still works even though the change of parameter is only 7-adic.

## Bounded searches on the remaining classes

We ran two kinds of bounded searches over the classes not ruled out by descent.

### Fixing two coefficients of $Y$

For each of the 7 singular orbit representatives that still have open classes, [quartic_free_mark.py](quartic_free_mark.py) sets $(Y_3, Y_4)$ to every admissible pair of rational numbers of height at most 16. Lifting to 46 base-7 digits and running rational reconstruction with height bound $10^{18}$ on the remaining coefficients finds zero identities across all 10,803 pairs (covering all three cube-root twists of $x$).

### Bounding $x$ alone

We can instead put a height bound only on $x$, leaving the coefficients of $y$ and $z$ completely unrestricted. After symmetry, the smooth classes and remaining singular classes leave 144,060 distinct abscissa vectors modulo 343. In a smooth class, [quartic_free_abscissas.py](quartic_free_abscissas.py) solves for the triple across all choices of the two free coefficients modulo 343. In a remaining singular class, two exact solutions over the same mod-49 triple satisfy $M\Delta_{\mathrm{fixed}} + N\Delta_{\mathrm{free}} \equiv 0 \pmod{49^2}$, where $N$ holds the two omitted columns. Since every column of $N$ lies in the mod-7 image of $M$ and $7M^{-1}$ is integral, $M^{-1}N$ is integral, which pins down the abscissa modulo 343 as an affine function of the two free digits.

Write the eight nonconstant coefficients of $x$ with a common positive denominator $d$ in lowest terms, defining height as $\max(d, |a_1|, \ldots, |a_8|)$. We test two bases:

1. The numerator coefficients of $X(t)$.
2. The Pell basis $(u - 1)^i$ ($1 \le i \le 4$) and $v(u - 1)^j$ ($0 \le j \le 3$).

At height bound 171, each mod-343 residue times $d$ has a unique centered lift per coefficient. At any odd prime not dividing $d$, both factors of $Z(Z + Y^2) = 2L^{12} - X^3$ have integral coefficients (by multiplicativity of the Gauss norm and their unit constant terms). Factoring $2L^{12} - X^3$ modulo a prime and checking whether complementary factors differ by a square is therefore a valid necessary test even with arbitrary denominators in $Y$ and $Z$. The sieve in [quartic_free_abscissas.cpp](quartic_free_abscissas.cpp) and factor-and-square test in [quartic_rational_search.py](quartic_rational_search.py) eliminate every candidate:

| Basis at height 171 | Primitive vectors after the mod-343 test | After testing at 3 and 5 where applicable | After also testing at 13, 11, 17, and 19 |
| --- | ---: | ---: | ---: |
| Numerator | 21,132,628 | 1,610,292 | 0 |
| Pell | 21,134,654 | 2,407,006 | 0 |

These counts are per basis and may overlap on the same rational abscissa. The height bound applies only to $x$.

## Changing the Pell conic and the integral seed

For squarefree integers $D > 1$, put $L_D = 1 - Dt^2$, $u = (1 + Dt^2)/L_D$, $v = 2t/L_D$, and repeat the factor-and-square sieve at each of the three seeds $(0, 1, 1)$, $(1, 0, 1)$, and $(-2, 3, 1)$. Both searches allow all mixed terms in $y$ and $z$ within the quartic degree bounds, skip any prime dividing the common denominator of $x$, and make no pole-retention assumption at 7:

* Setting $x = x_0 + \sum_{i=1}^4 a_i (u - 1)^i / d$ of exact degree 4 and height at most 6 gives 151,010 primitive vectors per seed. Congruence tests rule out every vector on all 18 squarefree conics $2 \le D \le 30$; see [even_abscissa_search.py](even_abscissa_search.py).
* Allowing all eight basis terms of $x - x_0$ with numerators in $\{-1, 0, 1\}$ and $1 \le d \le 6$ (requiring at least one nonzero $v$-term and at least one order-4 term) gives 34,668 vectors per seed. Congruence tests rule out all of them on all 49 squarefree conics $2 \le D \le 80$; see [mixed_conic_search.py](mixed_conic_search.py).

Run these commands from this directory to reproduce the computations:

```sh
uv run --with python-flint==0.9.0 python quartic_free_mark.py --height 16
uv run --with python-flint==0.9.0 python quartic_free_abscissas.py --height 171
uv run --with python-flint==0.9.0 python even_abscissa_search.py
uv run --with python-flint==0.9.0 python mixed_conic_search.py
lake -d .. build
```
