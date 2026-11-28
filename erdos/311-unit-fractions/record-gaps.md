# A lower bound on the error along a subsequence

Can $\delta(N)$ stay near its theoretical floor $1/\operatorname{lcm}(1, \ldots, N) = e^{-(1+o(1))N}$ for all large $N$? No—even without assuming that $-\log \delta(N)/N$ converges to a limit, we can force its **lower limit** $\sigma = \liminf_{N \to \infty} (-\log \delta(N))/N$ strictly below $0.813$, meaning $\delta(N) > e^{-0.813 N}$ infinitely often.

## Main theorem

Let $\delta(N)$ be the least nonzero distance from $1$ to a sum of distinct reciprocals with denominators at most $N$. Define
$$
\sigma := \liminf_{N \to \infty} \frac{-\log \delta(N)}{N}.
$$
Then
$$
\sigma \le \frac{190}{73 + \sqrt{25849}} = 0.8127429817\ldots
$$
In particular, $\delta(N) > e^{-0.813 N}$ for infinitely many $N$.

This argument extends Will Sawin's two-error bound of $\sigma \le 5/6 \approx 0.8333$ by comparing **three** consecutive record errors simultaneously. (Sawin's sharper bound of about $0.69$ assumes that the limiting rate exists.) [Sawin's discussion](https://www.erdosproblems.com/forum/thread/311)

---

## Proof strategy and basic tool

**The big idea.** Pick a sequence of "record" indices $n_1 < n_2 < \cdots$ where each new error drops by more than a factor of $4$ below the previous one. Clearing denominators at cutoff $X = n_j$ by $L = \operatorname{lcm}(1, \ldots, X)$ converts the last three record errors into three integers $(x, y, z)$ with $|x| > 4|y| > 16|z| > 0$.

Now form a list of distinct integer linear combinations of $x, y, z$ and take the product $V$ of all their pairwise differences:
* **Upper bound:** Because $|x|, |y|, |z|$ are tiny compared to $L$ (thanks to $\sigma$), $V$ is much smaller than $L^{\text{degree}}$.
* **Lower bound:** Modulo any large prime $p \in (X/3, X]$, each of $x, y, z$ can take only a handful of residue values (coming from multiples of $p$ up to $X$), which forces many collisions among our linear combinations and supplies high powers of $p$ dividing $V$.

The ratio $r = \limsup n_{j+1}/n_j$ controls the trade-off between two records and three records: a large $r$ weakens the two-record bound $\sigma \le 5/(2r + 4)$, while a small $r$ packs three records close together and tightens the three-record bound. Balancing the two curves gives the stated constant.

**Counting rule.** If two distinct integers agree modulo a prime $p$, their difference is a nonzero multiple of $p$. Therefore, if $m$ unordered pairs in a list of distinct integers agree modulo $p$, then $p^m$ divides the product of all pairwise differences of the list.

---

## Choosing the record errors

Start with $n_1 = 1$. Recursively define $n_{j+1}$ to be the **first** index at which the minimum error drops strictly below a quarter of the previous record:
$$
\delta(n_{j+1}) < \frac{\delta(n_j)}{4}.
$$
Such indices exist infinitely often because the power-of-two sums $1/2 + 1/4 + \cdots + 1/2^k = 1 - 2^{-k}$ approach $1$ arbitrarily closely.

For each $j$, fix a signed error $u_j = \sum_{a \in A_j} 1/a - 1$ (with $A_j \subseteq [1, n_j]$) attaining $|u_j| = \delta(n_j)$, and set $H_j = -\log |u_j|$. Because $n_{j+1}$ is minimal, at the preceding index $n_{j+1} - 1$ we still have $\delta(n_{j+1} - 1) \ge \delta(n_j)/4$. Applying the definition of $\sigma = \liminf (-\log \delta(N))/N$ at $N = n_{j+1} - 1$ gives
$$
H_j \ge (\sigma - o(1)) n_{j+1}.
$$
We may assume $\sigma > 4/5$ (otherwise the theorem holds trivially). Fix a large index $j$ and put
$$
X = n_j, \qquad U = n_{j-1}, \qquad L = \operatorname{lcm}(1, \ldots, X).
$$
Then
$$
(x, y, z) = L (u_{j-2}, u_{j-1}, u_j)
$$
are nonzero integers satisfying $|x| > 4|y|$ and $|y| > 4|z| > 0$. Throughout, we use the prime number theorem in the two forms $\log L = X + o(X)$ and $\sum_{p \le t} \log p = t + o(t)$.

---

## Step 1: Count with two errors

Consider any prime $p$ in the top dyadic range $X/2 < p \le X$. The *only* positive multiple of $p$ up to $X$ is $p$ itself, so each of $y$ and $z$ reduces modulo $p$ to either $0$ (if $p$ is omitted) or $L/p$ (if $p$ is included).

Among the three distinct integers $0, y, z$, at least two must share the same residue modulo $p$ (pigeonhole principle into $2$ values). Hence every prime $p \in (X/2, X]$ divides the nonzero product $yz(y - z)$. Comparing sizes:
* Lower bound: $\log \prod_{X/2 < p \le X} p = X/2 + o(X)$.
* Upper bound: $|y - z| \le 2|y|$, so $|yz(y - z)| \le 2 |y|^2 |z| = 2 L^3 e^{-2 H_{j-1} - H_j}$.

Taking logarithms yields
$$
H_j + 2 H_{j-1} \le \left(\frac{5}{2} + o(1)\right) X.
$$
Substituting $H_{j-1} \ge (\sigma - o(1)) X$ and $H_j \ge (\sigma - o(1)) n_{j+1}$ shows that the ratio $n_{j+1}/n_j$ stays bounded, so $r := \limsup_{j \to \infty} n_{j+1}/n_j$ is finite and satisfies
$$
\sigma (r + 2) \le \frac{5}{2}, \qquad \text{i.e.,} \qquad \sigma \le \frac{5}{2r + 4}.
$$
Since $n_{j+1} > n_j$ and $\sigma > 4/5$, this forces
$$
1 \le r \le \frac{5}{2\sigma} - 2 < \frac{25}{8} - 2 = \frac{9}{8}.
$$

---

## Step 2: Count with three errors

Now bring in the third record $x$ and form the six integers
$$
x, \quad y, \quad z, \quad x + y, \quad x + z, \quad y + z.
$$
All six are pairwise distinct, because in any difference between two of them, the largest term in the order $|x| > 4|y| > 16|z|$ strictly outweighs the remaining terms combined.

### Upper bound on the difference product $V$

Let $V$ be the absolute product of all $\binom{6}{2} = 15$ pairwise differences among these six integers. Group the $15$ differences by their largest surviving term:
* Three sums contain $x$ ($x, x+y, x+z$) and three omit $x$ ($y, z, y+z$), giving $3 \times 3 = 9$ cross-pairs whose leading term is $x$.
* Among the remaining $\binom{3}{2} + \binom{3}{2} = 6$ pairs, $4$ first differ at $y$ (namely $\{y, z\}$, $\{y+z, z\}$, $\{x+y, x\}$, $\{x+y, x+z\}$) and $2$ differ only at $z$ (namely $\{y, y+z\}$ and $\{x, x+z\}$).

Every difference has absolute value at most twice its leading term (since $|y| + |z| < \frac{1}{4}|x| + \frac{1}{16}|x| < |x|$ and $|z| < \frac{1}{4}|y|$). Therefore
$$
\log V \le 15 \log(2L) - 9 H_{j-2} - 4 H_{j-1} - 2 H_j.
$$

### Lower bound on $V$ from modulo-$p$ collisions

We inspect primes in two ranges below $X$:

* **Top range ($X/2 < p \le X$):** Divide the residues of $x, y, z$ modulo $p$ by the unit $L/p$ to obtain labels $(a, b, c) \in \{0, 1\}^3$. We claim at least **$6$ pairs** among the six sums $(a, b, c, a+b, a+c, b+c)$ coincide modulo $p$:
  * *Zero $1$s* $(0, 0, 0)$: all six sums equal $0$, giving $\binom{6}{2} = 15$ equal pairs.
  * *One $1$* (e.g., $(1, 0, 0)$): the six sums are $(1, 0, 0, 1, 1, 0)$—three $1$s and three $0$s, giving $\binom{3}{2} + \binom{3}{2} = 6$ equal pairs.
  * *Two $1$s* (e.g., $(1, 1, 0)$): the six sums are $(1, 1, 0, 2, 1, 1)$—four of them equal $1$, giving at least $\binom{4}{2} = 6$ equal pairs.
  * *Three $1$s* $(1, 1, 1)$: the six sums are $(1, 1, 1, 2, 2, 2)$—three $1$s and three $2$s, giving $\binom{3}{2} + \binom{3}{2} = 6$ equal pairs.

* **Middle range ($X/3 < p \le X/2$):** Now the available multiples of $p$ up to $X$ are $p$ and $2p$. Dividing residues modulo $p$ by the unit $L/(2p)$ turns $L/p \mapsto 2$ and $L/(2p) \mapsto 1$, giving labels $(a, b, c) \in \{0, 1, 2, 3\}^3$.
  * If some label is $0$ (say $a = 0$), then adding $a$ leaves the other two labels unchanged ($b = a + b$ and $c = a + c$), giving at least **$2$ equal pairs**.
  * If two labels are equal (say $a = b$), then they remain equal after adding the third ($a = b$ and $a + c = b + c$), again giving at least **$2$ equal pairs**.
  * Otherwise all three labels are nonzero and distinct, so they must be $\{1, 2, 3\}$ in some order, and $1 + 2 = 3$ still gives at least **$1$ equal pair**.
  * **Bonus on the subrange $U/2 < p \le X/2$:** Because the two older records $x, y$ only use denominators up to $U = n_{j-1} < 2p$, the multiple $2p$ is *unavailable* to them! Thus their labels lie in $\{0, 2\}$—which guarantees either a $0$ or a repetition $(2, 2)$, lifting the collision count from $1$ to **$2$ equal pairs**!

Because $U/X = n_{j-1}/n_j \ge 1/r - o(1) \ge 8/9 - o(1)$, we eventually have $U/2 > X/3$, so the subrange $(U/2, X/2]$ sits cleanly inside $(X/3, X/2]$. Summing the collision weights over $(X/2, X]$ (weight $6$, length $X/2$), $(X/3, X/2]$ (base weight $1$, length $X/6$), and the bonus on $(U/2, X/2]$ (extra weight $1$, length $(X - U)/2$), the counting rule and prime number theorem yield
$$
\log V \ge 6\!\left(\frac{X}{2}\right) + \frac{X}{6} + \frac{X - U}{2} + o(X)
= \frac{11}{3} X - \frac{U}{2} + o(X).
$$

Comparing our upper and lower bounds on $\log V$ (using $15 - 11/3 = 34/3$) gives
$$
2 H_j + 4 H_{j-1} + 9 H_{j-2} \le \frac{34}{3} X + \frac{U}{2} + o(X).
$$

---

## Step 3: Read off the constant

Pass to a subsequence of indices $j$ along which $n_{j+1}/X = n_{j+1}/n_j \to r$. Substituting the three lower bounds
$$
H_j \ge (\sigma - o(1)) n_{j+1} = (\sigma r - o(1)) X, \qquad
H_{j-1} \ge (\sigma - o(1)) X, \qquad
H_{j-2} \ge (\sigma - o(1)) U
$$
into our inequality and dividing by $X$ gives
$$
2 \sigma r + 4 \sigma + \left(9\sigma - \frac{1}{2}\right) \frac{U}{X} \le \frac{34}{3} + o(1).
$$
Since $9\sigma - 1/2 > 0$ and $U/X \ge 1/r - o(1)$ (by definition of $r = \limsup n_j/n_{j-1}$), replacing $U/X$ by $1/r$ yields
$$
2\sigma r + 4\sigma + \frac{9\sigma - 1/2}{r} \le \frac{34}{3}
\quad \Longrightarrow \quad
\sigma \le \frac{68r + 3}{12r^2 + 24r + 54}.
$$
Combining this with the two-record bound from Step 1 gives
$$
\sigma \le \min\!\left\{\frac{5}{2r + 4}, \; \frac{68r + 3}{12r^2 + 24r + 54}\right\}.
$$

On the interval $r \in [1, 9/8]$:
* $\frac{5}{2r + 4}$ is strictly **decreasing**.
* $\frac{68r + 3}{12r^2 + 24r + 54}$ is strictly **increasing**: the numerator of its derivative is $24(150 - 3r - 34r^2)$, which stays strictly positive on $[1, 9/8]$.

Therefore the minimum of the two curves attains its maximum where they intersect:
$$
\frac{5}{2r + 4} = \frac{68r + 3}{12r^2 + 24r + 54}
\quad \Longleftrightarrow \quad
38r^2 + 79r - 129 = 0.
$$
Eliminating $r = \frac{5}{2c} - 2$ shows that their common value $c = \sigma_{\max}$ is the positive root of the quadratic $54 c^2 + 73 c = 95$, namely
$$
c = \frac{-73 + \sqrt{73^2 + 4 \cdot 54 \cdot 95}}{108}
= \frac{190}{73 + \sqrt{25849}}
= 0.8127429817\ldots
$$
This completes the proof. $\square$
