# Ordinary polynomial parametrizations through an integral point

The simplest way to generate infinitely many integer solutions to $z^2 + y^2 z + x^3 = 2$ would be an **ordinary polynomial parametrization**: three polynomials $x, y, z \in \mathbb{Q}[t]$ solving the equation identically and taking integer values at some rational $t_0$. This document proves that no low-degree parametrization of this kind can exist:

> **Theorem.** Let $x, y, z \in \mathbb{Q}[t]$ satisfy $z^2 + y^2 z + x^3 = 2$ identically. Suppose $\deg x \le 5$ and all three polynomials take values integral at $13$ at some rational point $t_0$ (in particular, integer values). **Then $x, y, z$ are all constant.**

We also show why degree $6$ is the sharp boundary over $\mathbb{F}_{13}$, and exhibit an explicit family of rational polynomial curves ("osculating quadratic curves") that lie on the surface over $\mathbb{Q}[t]$ yet fail to hit even a single $13$-integral value of $y$. All finite-field checks below can be reproduced with [ordinary_polynomial_search.py](ordinary_polynomial_search.py).

## Proof strategy

1. **Blow up at $p = 13$:** Rescaling $t$ around $t_0$ clears all $13$-adic denominators (or pulls out any shared factor of $13$) without raising $\deg x$, producing a nonconstant polynomial solution over $\mathbb{F}_{13}[u]$ with $\deg x \le 5$.
2. **Pin down the allowed degrees:** Over $\mathbb{F}_{13}$, neither $2$ being a cube nor $2$ being a square holds. Factoring $z(z + y^2) = 2 - x^3$ then forces every irreducible factor of $z$ and $z + y^2$ to have degree divisible by $3$, leaving only four possible degree patterns for $1 \le \deg x \le 5$.
3. **Exhaust all candidates over $\mathbb{F}_{13}$:** We rule out $1 \le \deg x \le 4$ by **two completely independent methods** (factoring $2 - x^3$ vs. testing all $(x, y)$ pairs directly), and rule out $\deg x = 5$ by testing irreducible cubic factors of $2 - x^3$.

## Step 1: Reduction to a nonconstant map over $\mathbb{F}_{13}$

Shift $t_0$ to $0$, so all three constant terms are $13$-integral. Suppose at least one of $x, y, z$ is nonconstant, and define the balancing slope

$$
h = \max_{i > 0} \left(-\frac{v_{13}(a_i)}{i}\right)
$$

across all nonzero positive-degree coefficients $a_i$ of $x, y, z$. Write $h = r/s$ in lowest terms ($s > 0$) and adjoin a root $\pi$ of $\pi^s = 13$ to $\mathbb{Q}_{13}$. By Eisenstein's criterion, $\mathbb{Q}_{13}(\pi)$ is totally ramified with the same residue field $\mathbb{F}_{13}$.

Substitute $t = \pi^r u$. Even if $h \le 0$ (meaning all coefficients were already integral and possibly divisible by $13$), this substitution makes every coefficient integral and turns at least one positive-degree coefficient into a unit. Reducing modulo $\pi$ therefore produces a **nonconstant** solution over $\mathbb{F}_{13}[u]$ with $\deg x \le 5$.

## Step 2: Possible degrees over $\mathbb{F}_{13}[t]$

Work now in $\mathbb{F}_{13}[t]$ and set $z' = z + y^2$, so that

$$
zz' = 2 - x^3.
$$

Two elementary facts about $\mathbb{F}_{13}$ — $2$ is neither a cube ($\text{cubes} = \{0, \pm 1, \pm 5\}$) nor a square ($\text{squares} = \{0, 1, 3, 4, 9, 10, 12\}$) — severely restrict the degrees:

* **$x$ cannot be constant:** If $x$ is constant, then $zz' = 2 - x^3$ is a nonzero constant (since $2$ is not a cube mod $13$), forcing $z$, $z'$, and hence $y$ to be constant too. Thus $x$ is nonconstant, and neither $z$ nor $z'$ vanishes identically.
* **Every irreducible factor of $z$ or $z'$ has degree divisible by $3$:** At any root of an irreducible factor $p(t) \mid zz'$, the residue field $\mathbb{F}_{13}[t]/(p)$ contains a cube root of $2$. Because $X^3 - 2$ is irreducible over $\mathbb{F}_{13}$, the extension degree $\deg p$ must be a multiple of $3$.
* **Neither $z$ nor $z'$ can be constant:** If $z = z_0 \ne 0$ is constant, then $z_0 y^2 = 2 - z_0^2 - x^3$ defines a smooth genus-$1$ curve (smooth because $2 - z_0^2 \ne 0$, as $2$ is not a square mod $13$). A nonconstant polynomial map into that curve would embed its genus-$1$ function field inside the rational function field $\mathbb{F}_{13}(t)$, contradicting Lüroth's theorem. If $z'$ is constant, the exact same argument applies to $(x, y, -z')$.

Let $d = \deg x$. The degrees of $z$ and $z'$ are positive multiples of $3$ summing to $3d$. Whenever those two degrees differ, the larger one equals $\deg(z' - z) = 2\deg y$, so it must be **even**. Up to swapping $z$ and $z'$, the only allowed degree patterns for $d \le 5$ are:

| $d = \deg x$ | Degrees of $z, z'$ | Bound on $\deg y$ |
| --- | --- | --- |
| 1 | none | |
| 2 | 3, 3 | $\le 1$ |
| 3 | 3, 6 | $3$ |
| 4 | 6, 6 | $\le 3$ |
| 5 | 3, 12 | $6$ |

## Step 3: Two independent checks for $1 \le \deg x \le 4$

For $1 \le d \le 4$, we normalize $x$ by symmetries of $\mathbb{F}_{13}[t]$:

* Since $13 \nmid d$, shifting $t$ kills the $t^{d-1}$ coefficient of $x$.
* Scaling $t \mapsto at$ ($a \in \mathbb{F}_{13}^\times$) and twisting $x \mapsto \zeta x$ ($\zeta^3 = 1$) multiplies the leading coefficient of $x$ by $a^d \zeta$.

Keeping one leading coefficient per coset and varying all lower coefficients gives $1$, $26$, $169$, and $8{,}788$ candidates for $d = 1, 2, 3, 4$, respectively. (Some representatives may still be equivalent; we only need every equivalence class covered.)

We run **two independent verifications** across all candidates:

1. **Divisor-and-square test:** Factor $2 - x^3$ and list every monic divisor where both the divisor and its cofactor have degree at most $6$. For each of its $12$ nonzero scalar multiples $z$, check whether $(2 - x^3)/z - z$ is a square in $\mathbb{F}_{13}[t]$. This tests $9{,}776$ monic divisors ($117{,}312$ multiples) and finds **zero solutions**.
2. **Direct $(x, y)$-pair test (no factoring of $2 - x^3$):** Pair every normalized $x$ with every $y \in \mathbb{F}_{13}[t]$ of degree at most $3$. Evaluating $y^4 + 8 - 4x^3$ at all $13$ elements of $\mathbb{F}_{13}$ (requiring a quadratic residue at every point) filters $256{,}592{,}024$ pairs down to $11{,}156$ survivors. Squarefree factorization (including checking the leading scalar) confirms that **none** is a square. This completely avoids factoring $2 - x^3$ or enumerating $z$.

## Step 4: The quintic check ($\deg x = 5$) and sharpness at degree 6

For $d = 5$, $\gcd(5, 12) = 1$, so fifth powers cover all of $\mathbb{F}_{13}^\times$. Scaling and shifting therefore normalize $x$ to be **monic** with zero $t^4$ term, leaving $13^4$ choices for the four lower coefficients.

Replacing $z$ by $-z - y^2$ preserves the equation and swaps the roles of $z$ and $z'$, so by the table above we may assume $\deg z = 3$. Then $z$ must be a nonzero scalar multiple of an irreducible cubic factor of $2 - x^3$. Testing every cubic factor and every nonzero scalar in $\mathbb{F}_{13}^\times$ yields zero squares for $y^2$, completing the proof that $\deg x \ge 6$.

### Why degree 6 is sharp modulo 13

At $\deg x = 6$, solutions over $\mathbb{F}_{13}[t]$ genuinely appear! Writing coefficients in ascending order of degree ($c_0, c_1, \ldots$), one explicit example is:

* $x = (5, 5, 2, 5, 2, 0, 1)$,
* $y = (1, 4, 5, 0, 10)$,
* $z = (8, 4, 3, 7, 1, 2, 7, 5, 2, 5)$.

Direct polynomial multiplication confirms $z^2 + y^2 z + x^3 \equiv 2 \pmod{13}$.

## Osculating quadratic curves: rational solutions that miss 13-integral points

Why did our theorem require the curve to pass through a $13$-integral point? Because over $\mathbb{Q}[t]$ *without* an integral point, low-degree polynomial curves on $z^2 + y^2 z + x^3 = 2$ actually exist!

**Geometric construction:** Rewrite the surface by completing the square as $W^2 = y^4 + 8 - 4x^3$ (with $W = 2z + y^2$). Pick any rational point $(c, v)$ on the curve $v^2 = c^4 + 8$, and form the **osculating quadratic** $W(y)$ — the unique degree-$2$ Taylor approximation to $\sqrt{y^4 + 8}$ with second-order contact at $(c, v)$:

$$
W(y) = v + \frac{2c^3}{v}(y - c) + \left(\frac{3c^2}{v} - \frac{2c^6}{v^3}\right)(y - c)^2.
$$

Because $W(y)^2$ agrees with $y^4 + 8$ through order $(y - c)^2$, the difference $y^4 + 8 - W(y)^2$ is divisible by $(y - c)^3$, leaving just a linear factor! Explicitly, setting

$$
A = 3c^8 + 48c^4 - 64, \qquad B = c^8 - 48c^4 - 192,
$$

we obtain the exact contact identity:

$$
v^6 \bigl(y^4 + 8 - W(y)^2\bigr) = -8(y - c)^3 (Ay + cB).
$$

Now force the remaining factor $-2(Ay + cB)/v^6$ to be a cube $t^3$ by setting

$$
y = \frac{-v^6 t^3/2 - cB}{A}, \qquad x = t(y - c), \qquad z = \frac{W(y) - y^2}{2}.
$$

Here $A$ is nonzero for every rational $c$, and $(x, y, z)$ satisfies $z^2 + y^2 z + x^3 = 2$ identically over $\mathbb{Q}[t]$ (with $\deg x = 4$). Consistent with our degree-$6$ barrier, **every curve in this family misses even a $13$-integral value of $y$ at every rational $t$**! [Osculating.lean](Osculating.lean) certifies both the polynomial identity and this modulo-$13$ obstruction in Lean.

## Reproduce the finite checks

```sh
uv run --with python-flint==0.9.0 ordinary_polynomial_search.py
```
