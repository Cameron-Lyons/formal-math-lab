# A reciprocal-sum grid built with a variable number of prime intervals

Let $E_N$ be the sums of distinct reciprocals with positive denominators at most $N$, and let $\delta(N)$ be the least nonzero distance from $1$ to $E_N$. Write $L_0(t)=t$ and $L_{j+1}(t)=\log L_j(t)$, using natural logarithms. Let $B(t)$ be the product of $L_1(t),L_2(t),\ldots$ up to the last factor at least $2$. The empty product is $1$.

**Theorem.** For some absolute $c>0$ and every sufficiently large $N$, there is an integer $D$ such that
$$
\log D\ge c\frac{N}{B(N)},\qquad
\frac{s}{D}\in E_N\quad\text{for every integer }D/2\le s\le 3D/2.
$$
Taking $s=D\pm1$ gives both $1-1/D$ and $1+1/D$, and in particular $\delta(N)\le\exp(-cN/B(N))$. Whether $-\log\delta(N)/N$ tends to a positive constant remains open. [Erdős problem #311](https://www.erdosproblems.com/311)

## Adding a prime interval

Let $0\le a<1$. Suppose every grid point $m/D\in[a,3/2]$ is represented using distinct divisors of $D$ at most $H$ as denominators. Take primes coprime to $D$, with product $P$ and largest prime $z$. If $[aD,D]$ contains at least $z$ integers, we obtain a grid with
$$
D'=DP,\qquad a'=a+\sum_{p\mid P}\frac1p,\qquad H'=zH.
$$

Indeed, for each $s/(DP)\in[a',3/2]$, choose $m_p\in[aD,D]\cap\mathbb Z$ with $m_p(P/p)\equiv s\pmod p$. Subtract $\sum_{p\mid P}m_p/(pD)$. The remaining numerator over $DP$ is divisible by $P$, and each subtracted term is at most $1/p$, so the remainder is a grid point $m/D\in[a,3/2]$. Represent each $m_p/D$ on the old grid and multiply its denominators by $p$. The resulting groups are disjoint since each contains its own new prime and no other, while the denominators representing $m/D$ contain none. All denominators divide $DP$. [Prime extension lemma](README.md#how-to-add-primes-to-a-common-denominator)

## Choosing and adding the primes

For large $u$, write $y=\log u$ and take the primes in
$$
I(u)=\big(u/y^2,\ u(1+1/y)\big].
$$
Their product has logarithm at least $u+3$. Indeed $\vartheta(t)=\sum_{p\le t}\log p=t+O(t/\log^2t)$ gives $\sum_{p\in I(u)}\log p=u+u/y+O(u/y^2)$. Their reciprocal sum is at most $1/\sqrt y$ since $I(u)$ is covered by $O(\log y)$ dyadic intervals, each contributing $O(1/y)$ by $\pi(2w)\ll w/\log w$. Every prime in $I(u)$ lies between $2y$ and $u\exp(1/\sqrt y)$, and is at most $2u$, for all sufficiently large $u$. [Prime number estimates](https://arxiv.org/abs/2002.11068)

Starting at a large $x$, take successive logarithms down to the last scale in $[T,e^T)$, where $T$ is a sufficiently large absolute constant. Build the grid in reverse order. At the smallest scale, a fixed power of two $D_b\ge\exp(e^T+3)$ represents every grid point on $[0,3/2]$ by binary expansion using denominators $1,2,4,\ldots,D_b$. At each subsequent scale $u$, add the primes in $I(u)$. The total increase in the lower endpoint is at most
$$
\sum_{u}\frac1{\sqrt{\log u}}\le \frac2{\sqrt T}<\frac14.
$$
Here the sum runs over the prime extensions. Their successive values of $\log u$ increase by a factor of at least four, since $e^t\ge4t$ for $t\ge T$.

To check each extension, the preceding scale $y=\log u$ gives a current denominator $D'\ge\exp(y+3)=e^3u$ by the base choice or the prime product estimate. Its prime factors are at most $2y$, so the new primes are fresh. The lower endpoint stays below $1/4$, so the old grid covers $[1/2,1]$ and $[D'/2,D']$ contains at least $2u$ integers, enough for every new prime.

At scale $x$ the resulting $D$ is divisible by $4$, has $\log D\ge x+3$, and has all prime factors at most $2x$. Its grid covers $[1/2,3/2]$ using divisors of $D$. The product of the scales $u$ where primes were added is at most $xB(x)$, so the largest denominator used in a representation is at most
$$
D_b\prod_u \big(u\exp(1/\sqrt{\log u})\big)\le CxB(x),
\qquad C=e^{1/4}D_b.
$$

Finally take $x=N/(CB(N))$. Since $\log t\le t/2$ for $t\ge2$, the sum $\log B(N)=L_2(N)+L_3(N)+\cdots$ is at most $2L_2(N)$ for large $N$. Thus $x\to\infty$. Also $B$ is nondecreasing, so $CxB(x)\le N$. This proves the theorem with $c=1/C$.

The same estimate on $B$ gives $B(L_3(N))\le L_4(N)^2$. The exponent improves on the four-stage bound by a factor of at least a constant times $L_3(N)/L_4(N)^2$, which tends to infinity. [Four-stage construction](README.md#four-applications)
