# A quartic Pell substitution through one marked point

On the Pell conic $u^2 - 3v^2 = 1$, a **one-mark quartic substitution** is a triple of polynomial functions $(x, y, z)$ in $(u, v)$ of degree bounds $(4, 3, 6)$ solving $x^3 + y^2 z + z^2 = 2$ and hitting the single integer seed $(x, y, z) = (0, 1, 1)$ at $(u, v) = (1, 0)$. Any nonconstant rational example would generate infinitely many integer solutions ([MixedPellAmplification.lean](MixedPellAmplification.lean)).

A natural question is whether this problem is already obstructed **locally** over the $p$-adic fields $\mathbb{Q}_2$ or $\mathbb{Q}_3$. The calculations below give a mixed — and revealing — local picture, while leaving the general mixed quartic open over both $\mathbb{Q}_3$ and $\mathbb{Q}$:

| Setting | Result | Verification |
| --- | --- | --- |
| Over $\mathbb{Q}_2$ (general) | **Exists!** Explicit nonconstant $2$-adic solution | Lean ([OneMarkLocalTwo.lean](OneMarkLocalTwo.lean)) |
| Over $\mathbb{Q}_3$: ordinary polynomials of degrees $\le (4, 3, 6)$ | **Ruled out** (no nonconstant solution) | Python/FLINT ([local_quartic_three.py](local_quartic_three.py)) |
| Over $\mathbb{Q}_3$: quadratic graph $x = A(y-1)^2 + B(y-1)$ ($A \ne 0$) | **Ruled out** | Python/FLINT ([local_quartic_three.py](local_quartic_three.py)) |
| Over $\mathbb{Q}_3$: integral $t$-chart numerators ($L = 1 - 3t^2$) | $16$ nonconstant mod-$3$ classes survive to mod $81$ | Python ([quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py)) + Lean ([OneMarkLocalThree.lean](OneMarkLocalThree.lean)) |
| Over $\mathbb{Q}_3$: integral Pell-ring coefficients | $28$ nonconstant-mark pairs survive to mod $81$ | Python ([quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py)) |

## A nonconstant substitution over $\mathbb{Q}_2$

Over any field of characteristic zero, define the polynomials

$$
Y(s) = \frac{108s^3 - 239}{13}, \qquad
X(s) = \frac{2s(Y(s) - 1)}{3}, \qquad
Z(s) = \frac{44 - Y(s)^2 - 16Y(s)}{27}.
$$

Direct expansion shows that $X^3 + Y^2 Z + Z^2 = 2$ identically, with degrees $(4, 3, 6)$ in $s$. To hit the seed $(0, 1, 1)$, we want $Y(a) = 1$, which simplifies to $108a^3 = 252$, or

$$
3a^3 = 7.
$$

Quick sanity check: when $3a^3 = 7$, we get $Y(a) = (36 \cdot 7 - 239)/13 = 1$, $X(a) = 2a(1 - 1)/3 = 0$, and $Z(a) = (44 - 1 - 16)/27 = 1$.

Now solve $3a^3 - 7 = 0$ in $\mathbb{Z}_2$: at $s = 1$, $3s^3 - 7 = -4$ is even, while its derivative $9s^2 = 9$ is odd. By Hensel's lemma, there is an exact root $a \in \mathbb{Z}_2$ of $3a^3 = 7$. Setting $s = a + v$ produces a nonconstant quartic substitution over $\mathbb{Q}_2$ hitting $(0, 1, 1)$ at $v = 0$ (and $X(a + 1) \ne 0$). Lean proves the polynomial identity, the Hensel root in $\mathbb{Z}_2$, and $X(a + 1) \ne 0$ in [OneMarkLocalTwo.lean](OneMarkLocalTwo.lean).

## Two restricted classes ruled out over $\mathbb{Q}_3$

Both exclusions in this section are verified in [local_quartic_three.py](local_quartic_three.py).

### 1. Ordinary polynomials of degrees at most $(4, 3, 6)$

There is **no** nonconstant triple of ordinary polynomials in $\mathbb{Q}_3[t]$ of degrees at most $(4, 3, 6)$ taking the seed $(0, 1, 1)$ at $t = 0$. (Notice this contrasts sharply with $\mathbb{Q}_2$, where the polynomial construction $(X(a + v), Y(a + v), Z(a + v))$ succeeded!)

**Proof by $3$-adic slope balancing:**

1. Let $h = \max_{i>0}(-v_3(c_i)/i)$ over all nonzero positive-degree coefficients $c_i$, and rescale $t$ by an element of valuation $h$ in a totally ramified extension. The rescaled polynomials are $3$-integral with at least one nonconstant reduction, and every surviving positive index is a multiple of the reduced denominator of $h$.
2. If $X$ reduced to $0$, then $Z(Z + Y^2) = 2$ over $\mathbb{F}_3[t]$ would force $Y$ and $Z$ to be constant too, so $X$ must have a nonconstant reduction.
3. Exhaustive search over $\mathbb{F}_3$ finds $26$ reduced triples. Only $2$ of them are supported purely on even indices, and none is supported on multiples of $3, 4, 5$, or $6$ (larger denominators cannot occur within degree $6$). Thus $h$ must be either an **integer** or a **half-integer**:
   * **Integer $h$:** $24$ of the $26$ classes fail to lift modulo $9$. Each of the remaining $2$ has $177{,}147$ lifts modulo $81$, and **all** of them fail modulo $243$.
   * **Half-integer $h$:** Rescaling first by the integer part of $h$ puts the polynomials in the basis $t^i / 3^{\lfloor i/2 \rfloor}$. Checking the odd-index coefficients in this basis leaves $18$ classes modulo $3$, and every single one has a lifting correction matrix of rank $9$ with augmented rank $10$ (inconsistent).

As an immediate corollary, shifting any nonconstant linear Pell function $\ell$ to vanish at the mark also rules out all seeded triples of the form $(X(\ell), Y(\ell), Z(\ell))$ for ordinary polynomials of degrees at most $(4, 3, 6)$.

### 2. Quadratic graphs in $y$

Next, we rule out any relation of the form $x = A(y - 1)^2 + B(y - 1)$ with $A \ne 0$ over $\mathbb{Q}_3$.

Put $s = y - 1$ and complete the square in $z$ ($w = 2z + y^2$). The double cover

$$
w^2 = F(s) = (1 + s)^4 + 8 - 4(As^2 + Bs)^3
$$

must contain a component parametrized by the genus-$0$ Pell conic. Pulling out all square polynomial factors from $F(s)$ must therefore leave a squarefree part of degree at most $2$. Since $\deg F = 6$, the square factor has degree at least $4$ (from a polynomial of degree at least $2$), so $\deg\gcd(F, F') \ge 2$.

Now apply the Sylvester corank-$2$ discriminant trick:

1. Because $\deg\gcd(F, F') \ge 2$, the Sylvester matrix of $F$ and $F'$ has corank at least $2$, so its determinant and all its first cofactors vanish. Differentiating the determinant with respect to $B$ therefore yields zero as well.
2. Writing $\operatorname{disc}_s(F) = c A^3 D(A, B)$ strips out the nonzero factor $c A^3$, leaving $D(A, B) = \partial_B D(A, B) = 0$.
3. The leading coefficient of $D$ in $B$ is $59049 A \ne 0$, so $A$ must be a root of $\operatorname{disc}_B(D)$. Up to a constant and a power of $A$, $\operatorname{disc}_B(D)$ factors into powers of irreducible polynomials of degrees $6$, $24$, and $48$.
4. The $3$-adic Newton polygons of all three factors force every $3$-adic root to be a **$3$-adic unit**, yet the three factors have no unit roots modulo $9$, $3$, and $81$, respectively.

## Integral numerator chart at 3

Now allow general mixed quartic numerators in the rational $t$-chart with $L = 1 - 3t^2$ and $(x, y, z) = (X/L^4, Y/L^3, Z/L^6)$. Numerators in $\mathbb{Z}_3[t]$ have degrees at most $(8, 6, 12)$, constant terms $(0, 1, 1)$, and satisfy

$$
X^3 + Z(Y^2 + Z) = 2L^{12}.
$$

Unlike the restricted cases above, many residue classes survive high powers of $3$:

| Modulus | All surviving residues | Nonconstant reduced $X$ |
| --- | ---: | ---: |
| 3 | 759 | 758 |
| 9 | 21 | 20 |
| 27 | 19 | 18 |
| 81 | 17 | 16 |

* **Constant residue:** Lifts uniquely and trivially as $(0, L^3, L^6)$.
* **Nonconstant classes:** We first solve the linear system for $Y$ and $Z$ modulo $9$, and then inductively adjust $X$ by multiples of $3^k$ and $Y, Z$ by multiples of $3^{k+1}$ for $k \ge 1$. At order $3^{k+1}$, the condition is linear modulo $3$ with columns $X^2 t^i$, $2YZ t^i$, and $(Y^2 + 2Z) t^i$.
* **Why 2 classes vanish between 27 and 81:** In all $21$ mod-$3$ residues that lift to modulus $9$, the leading coefficients $a = X_8$, $b = Y_6$, and $c = Z_{12}$ all vanish modulo $3$. Comparing the $t^{24}$ coefficients then gives $a^3 + b^2 c + c^2 \equiv 0 \pmod{81}$. Since $3 \mid a, b, c$, we have $27 \mid a^3$ and $27 \mid b^2 c$, which forces $9 \mid c$, and then $81 \mid b^2 c + c^2$ forces $81 \mid a^3$, hence $9 \mid a$ too! That eliminates the $2$ classes lost between $27$ and $81$.

[quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py) verifies explicit lifts in every surviving class by direct multiplication, and [OneMarkLocalThree.lean](OneMarkLocalThree.lean) certifies the leading-coefficient implication ($a \equiv c \equiv 0 \pmod 9$) on integer representatives.

## Integral coefficients in the Pell ring at 3

To test $3$-integral polynomials in $(u, v)$ directly (without passing to the $t$-chart), write each degree-$d$ Pell function uniquely as

$$
f = P(v) + u Q(v), \qquad P, Q \in \mathbb{Z}_3[v], \quad \deg P \le d, \quad \deg Q < d.
$$

Because $u^2 = 1 + 3v^2 \equiv 1 \pmod 3$, the Pell conic splits modulo $3$ into two parallel lines: $u = +1$ (which contains the marked point $(1, 0)$) and $u = -1$. It is convenient to switch to the **component coordinates**

$$
f_+ = P + Q, \qquad f_- = P - Q,
$$

which have matching degree-$d$ coefficients (since $\deg Q < d$). Because $2$ is invertible in $\mathbb{Z}_3$, every pair $(f_+, f_-)$ with matching top coefficients corresponds uniquely to an integral Pell function $P + uQ$. Expanding $(P_f + uQ_f)(P_g + uQ_g)$ using $u^2 = 1 + 3v^2$ yields the exact componentwise product rule:

$$
(fg)_\pm = f_\pm g_\pm + \frac{3}{4} v^2 (f_+ - f_-)(g_+ - g_-).
$$

Modulo $3$, the two components decouple completely! Enumerating $Y$ and $Z$ over $\mathbb{F}_3[v]$ and taking the unique polynomial cube root for $X$ yields $27$ marked-component triples and $387$ unmarked-component triples. Matching their three degree-$(4, 3, 6)$ leading coefficients produces $1{,}161$ pairs, of which $56$ lift modulo $9$:

| Marked component modulo 3 | Pairs lifting to 9 |
| --- | ---: |
| $(0, 1, 1)$ | 20 |
| $(-v^2, 1, 1 + v^3)$ | 18 |
| $(-v^2, 1, 1 - v^3)$ | 18 |

* Among the $36$ pairs with a **nonconstant** marked component, $28$ lift to modulus $27$ and all $28$ continue to lift to modulus $81$; [quartic_one_mark_three_lifts.py](quartic_one_mark_three_lifts.py) checks the full polynomial identity modulo $81$ for each of them.
* For the $20$ pairs with a **constant** marked component $(0, 1, 1)$, the census stops at modulus $9$ (note that a nonconstant $3$-adic function can still reduce to a constant modulo $3$).
