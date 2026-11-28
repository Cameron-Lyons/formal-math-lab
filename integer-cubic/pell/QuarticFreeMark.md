# Quartic Pell substitutions through one integer point

On the Pell conic $u^2 - 3v^2 = 1$, parametrize points rationally by setting

$$
L = 1 - 3t^2, \qquad u = \frac{1 + 3t^2}{L}, \qquad v = \frac{2t}{L}.
$$

We search for a **quartic Pell substitution** passing through the single integer seed $(0, 1, 1)$ at $t = 0$:

$$
(x, y, z) = \left(\frac{X}{L^4}, \frac{Y}{L^3}, \frac{Z}{L^6}\right), \qquad X^3 + ZY^2 + Z^2 = 2 L^{12},
$$

where $X, Y, Z \in \mathbb{Q}[t]$ have degrees at most $8, 6, 12$, constant terms $0, 1, 1$, and $X \ne 0$.

Why is this family such a prime target? In [MixedPellAmplification.lean](MixedPellAmplification.lean), Lean proves (`SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`) that **any** such rational identity automatically generates **infinitely many integer solutions** to $z^2 + y^2 z + x^3 = 2$ (and the same holds for any integral seed with nonconstant $x$). The amplification works by choosing a subsequence of powers of the fundamental Pell unit $2 + \sqrt{3}$ whose coordinates clear all denominators of the rational coefficients while preserving the seed congruence modulo those denominators.

This document establishes two major partial exclusions for the seed $(0, 1, 1)$:

1. **Height-free $7$-adic descent:** Assuming $7$-integral coefficients and full poles modulo $7$, **more than half** ($2{,}352$ out of $4{,}410$) of the singular mod-$49$ residue classes that lift to mod $343$ are **unconditionally impossible at every coefficient height** — which in particular rules out every quartic chart where $x$ depends only on $u$ (for any $7$-adic nonsquare unit $D$).
2. **Bounded searches on all remaining classes:** Exact modular sieves eliminate every candidate with $(Y_3, Y_4)$ of height $\le 16$ ($10{,}803$ pairs), every candidate with $x$ of height $\le 171$ and **completely unrestricted $y, z$** (over $21$ million primitive vectors in each of two bases), and small-height candidates across $18$ and $49$ squarefree Pell conics $D$ at three seeds.

## Height-free descent from the singular residues at 7

Assume the coefficients of $X, Y, Z$ are integral at $7$ and $\gcd(\bar X, \bar L) = 1$ modulo $7$. Modulo $7$, there are $66$ valid triples through $(0, 1, 1)$:

* $18$ are **smooth** (Jacobian rank $24$), and
* $48$ are **singular** (Jacobian rank $20$).

Over those $48$ singular mod-$7$ classes, exactly $4{,}410$ triples modulo $49$ lift further to modulus $343$.

> **Theorem.** Of those $4{,}410$ singular mod-$49$ classes, **$2{,}352$ cannot come from a rational identity of any coefficient height**.

* **Verification split:** The modular counts and Jacobian ranks are exact FLINT calculations in [quartic_first_lifts.py](quartic_first_lifts.py) and [quartic_free_mark.py](quartic_free_mark.py), while Lean checks the characteristic-zero descent and contradiction in [QuarticPullbackDescent.lean](QuarticPullbackDescent.lean) and [QuarticSparse.lean](QuarticSparse.lean).

### Step 1: The 2,352 classes match a sparse composition family

Set $S = (ct + dt^2)/L$ and consider the **sparse composition**

$$
x = 3S^4 + bS, \qquad y = 1 + C S^3, \qquad z = 1 + F S^3 + E S^6.
$$

For any nonconstant $S$, the cubic surface identity $x^3 + y^2 z + z^2 = 2$ reduces to four algebraic equations in the four scalars $(b, C, F, E)$:

$$
\begin{aligned}
b^3 + 2C + 3F &= 0, \\
3E + (F + C)^2 + 9b^2 &= 0, \\
2(F + C)E + C^2 F + 27b &= 0, \\
E^2 + C^2 E + 27 &= 0.
\end{aligned}
$$

At $(b, C, F, E) \equiv (0, 3, -2, 2) \pmod 7$, the $4 \times 4$ Jacobian of this system is invertible modulo $7$. Hensel lifting yields a unique solution in $\mathbb{Z}_7^4$, congruent to $(14, 38, 40, 30) \pmod{49}$; in particular $bC \ne 0$.

Up to the symmetries $t \mapsto -t$ and twisting $x$ by a cube root of unity, every rank-$20$ residue modulo $7$ comes from one of these sparse compositions. For each choice of $(c, d) \bmod 7$, its $49$ lifts modulo $49$ produce $49$ distinct triples, giving $48 \cdot 49 = 2{,}352$ mod-$49$ classes in total.

### Step 2: Every exact $\mathbb{Z}_7$-lift in these 2,352 classes is trapped in the sparse family

Why can't a genuine non-sparse solution merely *agree* with a sparse composition modulo $49$ and peel away at higher powers of $7$? Because the Jacobian is nearly invertible (its determinant has valuation only $4$, so $7M^{-1}$ is integral), giving a superlinear contraction:

1. **Tune $(c, d)$ to match two coefficients of $Y$:** Choose two distinguishing coefficients of $Y$:
   * use $(Y_3, Y_4)$ when $c \not\equiv 0 \pmod 7$ (with variable parts $Cc^3, 3Cc^2 d$), or
   * use $(Y_5, Y_6)$ when $c \equiv 0 \pmod 7$ (with variable parts $3Ccd^2, Cd^3$ and $d \not\equiv 0 \pmod 7$).

   In both cases, the $2 \times 2$ Jacobian with respect to $(c, d)$ is invertible modulo $7$, so by Hensel's lemma we can tune $(c, d) \in \mathbb{Z}_7^2$ so that the sparse composition matches those two exact coefficients of any given $\mathbb{Z}_7$-lift. Because those two coordinates already separate all $49$ compositions modulo $49$, all remaining $24$ coefficients automatically agree modulo $49$ as well.
2. **Contraction on the remaining 24 unknowns:** Hold those two coefficients fixed and let $M$ be the $24 \times 24$ Jacobian in the remaining $24$ unknowns. In every listed mod-$49$ class, $M$ has rank $20$ modulo $7$ and $v_7(\det M) = 4$, which implies that **$7M^{-1}$ has entries in $\mathbb{Z}_7$**. Perturbing $M$ by any multiple of $49$ preserves this property because $M^{-1}(M' - M)$ is divisible by $7$.
3. **Force $\Delta = 0$:** Suppose two exact solutions sharing those two fixed coordinates differ by a vector $\Delta$ divisible by $7^k$ ($k \ge 2$). Taylor expansion gives $M\Delta \in 7^{2k}\mathbb{Z}_7^{24}$; multiplying by $7M^{-1} \in \mathbb{Z}_7^{24 \times 24}$ gives $\Delta \in 7^{2k-1}\mathbb{Z}_7^{24}$. Since $2k - 1 > k$ for all $k \ge 2$, iterating this step forces $\Delta = 0$!

### Step 3: Descent from $\mathbb{Q}_7$ to $\mathbb{Q}$ and contradiction

Now assume the original chart has **rational** coefficients. Pick any two rational values of $t$ where $r = y - 1$ takes distinct nonzero rational values. Because the chart equals a sparse composition over $\mathbb{Z}_7$, the matching rational values of $z$ satisfy

$$
z - 1 = \frac{F}{C} r + \frac{E}{C^2} r^2.
$$

Two distinct nonzero points determine a quadratic through the origin uniquely, forcing $k = F/C$ and $\ell = E/C^2$ to be **rational**. From the first equation above, $g = b^3/C = -2 - 3k$ is rational and nonzero. Rescaling the parameter to $T = bS$ turns the sparse composition into a purely **rational** identity:

$$
x = T - \frac{3\ell + (k + 1)^2}{3g^2} T^4, \qquad
y = 1 + \frac{T^3}{g}, \qquad
z = 1 + \frac{k}{g} T^3 + \frac{\ell}{g^2} T^6.
$$

The same calculation works after twisting $x$ by a cube root of unity, using the twisted linear coefficient to define $T$. Lean proves in [QuarticPullbackDescent.lean](QuarticPullbackDescent.lean) that these rational coefficient equations contradict the sparse-quartic obstruction already proved in [QuarticSparse.lean](QuarticSparse.lean).

The remaining $2{,}058$ singular mod-$49$ classes and $18$ smooth rank-$24$ classes modulo $7$ are not covered by this descent.

### Consequence: $x$ cannot depend on $u$ alone

> **Corollary.** Suppose $D$ is a $7$-adic unit with nonsquare residue modulo $7$, and consider $u^2 - Dv^2 = 1$ with $L_D = 1 - Dt^2$ and the seed $(0, 1, 1)$. If the chart coefficients are integral at $7$ and both poles of $x$ keep order $4$ modulo $7$, then **$x$ cannot be a polynomial in $u$ alone** (equivalently, $X(t)$ cannot be an even polynomial).

**Proof:** Since $D/3$ is a square in $\mathbb{Z}_7^\times$, rescaling $t \mapsto \sqrt{D/3}\,t$ identifies the chart at $7$ with the $D = 3$ chart while preserving evenness of $X$. Among the $12$ residue orbits modulo $7$, only three singular representatives — $(c, d) = (0, 1), (0, 6), (1, 0)$ — have even $X \bmod 7$:

* in $(0, 1)$ and $(0, 6)$, **every** lift is a sparse composition;
* in $(1, 0)$, all $49$ non-composition classes satisfy $X_1 \equiv 14 \pmod{49}$ before symmetry, and neither twisting $x$ nor reflecting $t$ can make $X_1 = 0$.

Thus any even $X$ is forced into a sparse composition, and the rational descent in Step 3 uses only two rational evaluations of the original $y$ and $z$, so it still applies even though the parameter rescaling $\sqrt{D/3}$ is only $7$-adic.

## Bounded searches on the remaining classes

To probe the $2{,}058$ remaining singular mod-$49$ classes and $18$ smooth mod-$7$ classes, we ran two complementary bounded searches.

### 1. Fixing two coefficients of $Y$ (height $\le 16$)

For each of the $7$ singular orbit representatives that still contain open classes, [quartic_free_mark.py](quartic_free_mark.py) sets $(Y_3, Y_4)$ to every admissible pair of rational numbers of height at most $16$, lifts the remaining coefficients to $46$ base-$7$ digits, and applies rational reconstruction with height bound $10^{18}$. Across all $10{,}803$ pairs (covering all three cube-root twists of $x$), **zero** rational identities appear.

### 2. Bounding $x$ alone (height $\le 171$, unrestricted $y$ and $z$)

Even better, we can put a height bound **solely on $x$**, leaving the coefficients and denominators of $y$ and $z$ completely unrestricted!

1. **Pinning $x$ modulo $343$:** After symmetry, the smooth classes and remaining singular classes yield $144{,}060$ distinct abscissa vectors modulo $343$.
   * In a **smooth** class, [quartic_free_abscissas.py](quartic_free_abscissas.py) solves directly for the triple across all choices of the two free coefficients modulo $343$.
   * In a **remaining singular** class, two exact solutions over the same mod-$49$ triple satisfy $M\Delta_{\mathrm{fixed}} + N\Delta_{\mathrm{free}} \equiv 0 \pmod{49^2}$, where $N$ holds the two omitted columns. Because every column of $N$ lies in the mod-$7$ image of $M$ and $7M^{-1}$ is integral, $M^{-1}N$ is integral, which pins down the abscissa modulo $343$ as an affine function of the two free digits!
2. **Height convention and two bases:** Write the eight nonconstant coefficients of $x$ with a common positive denominator $d$ in lowest terms, defining the height as $\max(d, |a_1|, \ldots, |a_8|)$. We test two bases:
   * **Numerator basis:** the eight nonconstant coefficients of $X(t)$;
   * **Pell basis:** $(u - 1)^i$ ($1 \le i \le 4$) and $v(u - 1)^j$ ($0 \le j \le 3$).

   At height bound $171$, $2 \cdot 171 < 343$, so each mod-$343$ residue multiplied by $d$ has a **unique** centered integer lift per coefficient!
3. **Why modular filtering works despite arbitrary denominators in $y, z$:** At any odd prime $p \nmid d$, the polynomial $2L^{12} - X^3 = Z(Z + Y^2)$ is $p$-integral, and both factors $Z$ and $Z + Y^2$ have unit constant terms ($1$ and $2$). By multiplicativity of the Gauss norm, **both factors must be $p$-integral** even if $Y$ and $Z$ have huge denominators elsewhere! Factoring $2L^{12} - X^3$ modulo $p$ and checking whether complementary divisors differ by a square is therefore a rigorous necessary test regardless of the height of $Y$ and $Z$.

The C++ sieve in [quartic_free_abscissas.cpp](quartic_free_abscissas.cpp) and factor-and-square test in [quartic_rational_search.py](quartic_rational_search.py) eliminate every single candidate:

| Basis at height 171 | Primitive vectors after the mod-343 test | After testing at 3 and 5 where applicable | After also testing at 13, 11, 17, and 19 |
| --- | ---: | ---: | ---: |
| Numerator | 21,132,628 | 1,610,292 | 0 |
| Pell | 21,134,654 | 2,407,006 | 0 |

(Counts are per basis and may overlap on the same rational abscissa; the height bound applies exclusively to $x$.)

## Changing the Pell conic and the integral seed

Finally, for squarefree integers $D > 1$, put $L_D = 1 - Dt^2$, $u = (1 + Dt^2)/L_D$, $v = 2t/L_D$, and repeat the factor-and-square sieve at each of the three integer seeds $(0, 1, 1)$, $(1, 0, 1)$, and $(-2, 3, 1)$. Both searches allow arbitrary mixed terms in $y$ and $z$ within the quartic degree bounds, skip any prime dividing the common denominator of $x$, and make **no** pole-retention assumption at $7$:

* **Even abscissas (height $\le 6$):** Setting $x = x_0 + \sum_{i=1}^4 a_i (u - 1)^i / d$ of exact degree $4$ and height at most $6$ gives $151{,}010$ primitive vectors per seed. Congruence tests rule out every vector on all $18$ squarefree conics $2 \le D \le 30$; see [even_abscissa_search.py](even_abscissa_search.py).
* **Mixed abscissas (numerators in $\{-1, 0, 1\}$, $1 \le d \le 6$):** Allowing all eight basis terms of $x - x_0$ with numerators in $\{-1, 0, 1\}$ and $1 \le d \le 6$ (requiring at least one nonzero $v$-term and at least one order-$4$ term) gives $34{,}668$ vectors per seed. Congruence tests rule out all of them on all $49$ squarefree conics $2 \le D \le 80$; see [mixed_conic_search.py](mixed_conic_search.py).

## Reproduce the computations

Run these commands from this directory:

```sh
uv run --with python-flint==0.9.0 python quartic_free_mark.py --height 16
uv run --with python-flint==0.9.0 python quartic_free_abscissas.py --height 171
uv run --with python-flint==0.9.0 python even_abscissa_search.py
uv run --with python-flint==0.9.0 python mixed_conic_search.py
lake -d .. build
```
