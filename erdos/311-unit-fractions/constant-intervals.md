# Long intervals with the same attainable sums near 1

Although $\delta(n)$ shrinks overall as more unit fractions become available, it does not shrink smoothly: it stays completely flat across surprisingly long runs of consecutive integers, even inside short intervals $[Y, Y + Y^\eta]$.

Let $J_n = E_n \cap [3/4, 5/4]$ be the set of sums in $[3/4, 5/4]$ of distinct reciprocals with denominators at most $n$, and let $\delta(n)$ be the least nonzero distance from $1$ to $J_n$. (For $n \ge 4$ this agrees with the global minimum over all of $E_n$, since $1 + 1/n \in J_n$.)

**Theorem.** Fix $0 < \eta \le 1$. For every sufficiently large $Y$, the interval $[Y, Y + Y^\eta]$ contains a block of consecutive integers of length
$$
\gg_\eta \frac{\log Y}{\log\log\log Y}
$$
on which $J_n$—and hence $\delta(n)$—is constant.

---

## Proof strategy

From the [cofactor upper bound for change indices](change-indices.md#an-upper-bound-on-the-cofactor), for all large $Y$, an integer $n \in (Y, 2Y]$ can satisfy $J_n \ne J_{n-1}$ **only if** $n$ is a prime power times a small cofactor:
$$
n = j p^a, \qquad p \text{ prime}, \quad a \ge 1, \quad j \le T := C \log Y \, (\log\log Y)^5,
$$
where $C$ is an absolute constant.

**How do we forbid this factorization for $H$ consecutive integers at once?** Suppose an integer $n \in (Y, 2Y]$ has a divisor $d$ satisfying three properties:
1. $d > T$,
2. $d$ is small compared to $Y$ (polynomial in $\log Y$, so $Td < Y$), and
3. $\gcd(d, n/d) = 1$ (so $d$ and its complementary factor share no primes).

Then $n = j p^a$ with $j \le T$ is **impossible**:
* If $p \nmid d$, then $d$ must divide $j$, contradicting $d > T$.
* If $p \mid d$, then $\gcd(d, n/d) = 1$ forces the *entire* $p$-part $p^a$ of $n$ to divide $d$, so $p^a \le d$ and therefore $n = j p^a \le T d < Y$, contradicting $n > Y$!

To create $H$ consecutive integers $Z + (A+1), \ldots, Z + (A+H)$ with this property simultaneously, we simply pick $A > T$, let $L = \operatorname{lcm}(A+1, \ldots, A+H)$, and choose $Z$ to be a multiple of $L^2$ near $Y$. Then for every $d = A + i$, $d^2 \mid Z$ guarantees
$$
\frac{Z + d}{d} = \frac{Z}{d} + 1 \equiv 1 \pmod d \implies \gcd\!\left(d, \frac{Z+d}{d}\right) = 1!
$$
All that remains is to make $H$ as large as possible while keeping $L^2 \le Y^{\eta/2}$ so that the block fits comfortably inside $[Y, Y + Y^\eta]$.

---

## Choosing consecutive divisors

Write $M = \log Y$, and set
$$
A = \left\lceil M (\log M)^6 \right\rceil, \qquad
H = \left\lfloor \frac{\eta M}{30 \log\log M} \right\rfloor, \qquad
L = \operatorname{lcm}(A + 1, \ldots, A + H).
$$
Notice that $A > T$ for large $Y$ (since $(\log M)^6$ beats $C (\log M)^5$), while $H \asymp_\eta \log Y / \log\log\log Y$.

### Bounding $L$ via a binomial coefficient

We claim the exact divisibility
$$
L \ \bigm|\ \operatorname{lcm}(1, \ldots, H) \binom{A + H}{H}.
$$

*Proof of the divisibility.* Fix any prime $p$, and let $p^v$ be the largest power of $p$ dividing any integer in the block $\{A + 1, \ldots, A + H\}$. Set $s = \lfloor \log H / \log p \rfloor$, so $p^s$ is the exact power of $p$ dividing $\operatorname{lcm}(1, \ldots, H)$.
* If $v \le s$, then $\operatorname{lcm}(1, \ldots, H)$ already supplies $p^v$.
* If $v > s$, then $\operatorname{lcm}(1, \ldots, H)$ supplies $p^s$, and we need $\binom{A+H}{H}$ to supply at least $p^{v - s}$. By Legendre's formula,
  $$
  v_p\!\left(\binom{A+H}{H}\right) = \sum_{b \ge 1} \left( \left\lfloor \frac{A+H}{p^b} \right\rfloor - \left\lfloor \frac{A}{p^b} \right\rfloor - \left\lfloor \frac{H}{p^b} \right\rfloor \right).
  $$
  Every term in this sum is nonnegative (any $H$ consecutive integers contain at least $\lfloor H/p^b \rfloor$ multiples of $p^b$). Moreover, for each exponent $s < b \le v$:
  * $H < p^b$, so $\lfloor H/p^b \rfloor = 0$ ($H!$ contains no multiple of $p^b$); while
  * the block $\{A + 1, \ldots, A + H\}$ *does* contain a multiple of $p^b$ (by definition of $v$), so $\lfloor (A+H)/p^b \rfloor - \lfloor A/p^b \rfloor \ge 1$.

  Each of the $v - s$ exponents $b \in (s, v]$ therefore contributes at least $1$ to $v_p(\binom{A+H}{H})$, giving total $p$-adic valuation at least $s + (v - s) = v$ on the right-hand side. $\square$

### Estimating $\log L$

By the prime number theorem, $\log \operatorname{lcm}(1, \ldots, H) = O(H)$. Using the standard bound $\binom{A+H}{H} \le (e(A+H)/H)^H$, we get
$$
\log L \le O(H) + H \log \frac{e(A+H)}{H} \le \left(\frac{\eta}{5} + o(1)\right) M.
$$
Indeed, for fixed $\eta > 0$,
$$
\frac{e(A+H)}{H} \asymp_\eta (\log M)^6 \log\log M \implies \log \frac{e(A+H)}{H} = (6 + o(1)) \log\log M,
$$
and multiplying by $H \le \frac{\eta M}{30 \log\log M}$ gives $\frac{6}{30}\eta M = \frac{\eta}{5} M$. In particular, for all sufficiently large $Y$,
$$
\log(L^2) \le \frac{\eta}{2} M \implies L^2 \le Y^{\eta/2}.
$$

---

## Excluding changes throughout the block

Let $Z = L^2 \lceil Y / L^2 \rceil$ be the smallest multiple of $L^2$ that is at least $Y$. Since $Y \le Z < Y + L^2 \le Y + Y^{\eta/2}$ and $A + H$ grows only polynomially in $\log Y$, all $H + 1$ consecutive integers
$$
Z + A, \; Z + A + 1, \; \ldots, \; Z + A + H
$$
lie inside $[Y, Y + Y^\eta]$ (and in particular inside $[Y, 2Y]$) for all sufficiently large $Y$.

Now fix any $1 \le i \le H$, put $d = A + i$, and write $n = Z + d$:
1. Since $d \mid L$, we have $d^2 \mid L^2 \mid Z$. Thus $n/d = Z/d + 1 \equiv 1 \pmod d$, which proves $\gcd(d, n/d) = 1$.
2. Also $d > A > T$ for large $Y$, while $T d \le T(A + H) = O((\log Y)^2 (\log\log Y)^{11}) < Y$.
3. Suppose for contradiction that $n = j p^a$ with $p$ prime, $a \ge 1$, and $j \le T$:
   * If $p \nmid d$, then $\gcd(d, p^a) = 1$, so $d \mid j$, contradicting $d > T \ge j$.
   * If $p \mid d$, then $\gcd(d, n/d) = 1$ forces $p^a \mid d$, hence $p^a \le d$ and $n = j p^a \le T d < Y$, contradicting $n > Y$.

Therefore $n$ fails the necessary condition for a change index, so $J_n = J_{n-1}$ for all $i = 1, \ldots, H$. This gives a block of $H + 1 \gg_\eta \log Y / \log\log\log Y$ consecutive integers on which $J_n$ (and thus $\delta(n)$) is constant, proving the theorem. $\square$

---

## Consequence for a linear approximation

Write $F(n) = -\log \delta(n)$. On the constructed block $[Z + A, Z + A + H]$, $F(n)$ is constant, whereas any linear function $cn + b$ with fixed slope $c > 0$ grows by $cH$ from one end of the block to the other. Thus the residuals $F(n) - cn - b$ at the two endpoints differ by $cH$, so at least one endpoint has residual magnitude at least $cH/2$:
$$
\max_{n \in [Y, Y + Y^\eta] \cap \mathbb{Z}} |F(n) - cn - b|
\ge \frac{cH}{2}
\gg_{\eta, c} \frac{\log Y}{\log\log\log Y}.
$$
This rules out any linear approximation $-\log \delta(n) = cn + b + o(\log n / \log\log\log n)$ of positive slope. Erdős and Graham's conjectured limit $-\log \delta(n)/n \to c$ allows an error of $o(n)$, which easily accommodates these constant stretches. [Erdős Problem #311](https://www.erdosproblems.com/311)
