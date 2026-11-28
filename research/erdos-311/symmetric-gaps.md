# Symmetric gaps around 1

Let $E_N$ be the set of sums of distinct reciprocals with denominators in $\{1,\ldots,N\}$. Write $\delta_{\rm sym}(N)$ for the smallest $e>0$ such that both $1-e$ and $1+e$ belong to $E_N$. For $N\ge2$ the pair $1/2,3/2$ gives $\delta_{\rm sym}(N)\le1/2$.

## Why the exponential rate is zero

Add the two representations. The errors cancel, giving
$$
\sum_{n=1}^N\frac{c_n}{n}=2,\qquad c_n\in\{0,1,2\}.
$$
Let $Q$ be the least common multiple of the denominators used. Since $e$ is a positive multiple of $1/Q$, it suffices to bound $\log Q$.

Take any prime $p\mid Q$, put $k=\lfloor N/p\rfloor$, and write $\Lambda_k=\operatorname{lcm}(1,\ldots,k)$. Multiply the identity by $p\Lambda_k$ and reduce modulo $p$. Only terms with $n=pj$ survive, so $p$ divides the positive integer
$$
m=\sum_{j=1}^k c_{pj}\frac{\Lambda_k}{j}\le 2k\Lambda_k.
$$
Chebyshev's prime-counting bound gives $\log\Lambda_k\le\pi(k)\log k=O(k)$, since each prime power in the least common multiple is at most $k$. Thus $\log p\le\log m=O(N/p)$, and every participating prime satisfies $p\ll N/\log N$ (split at $p=\sqrt N$). This is the large-prime argument of Martin's Lemma 8 with multiplicities up to two. [Martin, *Denser Egyptian fractions*, §3](https://matwbn.icm.edu.pl/ksiazki/aa/aa95/aa9533.pdf)

By $\pi(x)\ll x/\log x$, there are $O(N/(\log N)^2)$ such primes. Each contributes at most $\log N$ to $\log Q$, since its highest power in $Q$ divides some $n\le N$. Therefore
$$
-\log\delta_{\rm sym}(N)\ll \frac{N}{\log N},
\qquad
\lim_{N\to\infty}\frac{-\log\delta_{\rm sym}(N)}{N}=0.
$$
Erdős #311 asks about a single approximation. For example, at $N=4$ the closest sum different from 1 is $13/12=1/2+1/3+1/4$, whereas the closest symmetric pair is $3/4,5/4$. These values follow by taking subset sums of $12,6,4,3$ and dividing by $12$. [Erdős problem #311](https://www.erdosproblems.com/311)

## The sharper estimate

Write $\ell_j=\log_j N$ and let $B(N)$ be the product of the successive iterated logarithms that are at least $2$. Then
$$
\frac{N}{B(N)}\ll -\log\delta_{\rm sym}(N)
\ll \frac{N\ell_3}{\ell_1\ell_2},
\qquad
-\log\delta_{\rm sym}(N)=\frac{N}{\ell_1\ell_2^{1+o(1)}}.
$$

For the lower bound, the grid construction represents every $s/D\in[1/2,3/2]$ with $\log D\gg N/B(N)$. Take $s=D-1,D+1$. The same grid gives $\log D_*\gg N/B(N)$ for the largest complete grid denominator $D_*$. [Grid construction](iterated-grid.md) · [Largest complete grid](largest-grid.md)

For the upper bound, use one cutoff $K=\lfloor\eta\ell_1\ell_2/\ell_3\rfloor$ for all large primes, with $\eta>0$ a small absolute constant. If $p>y=N/(K+1)$ divides $Q$, then $\lfloor N/p\rfloor\le K$. The same divisibility argument with $\Lambda_K$ shows that $p$ divides some positive integer in $\Lambda_K(E_K+E_K)$, because the coefficients $c_{pj}$ come from two subsets. There are at most $|E_K|^2$ such integers, each at most $2K\Lambda_K$. The logarithm of their product is $O(K|E_K|^2)$. Chen uses a related prime-divisor count for differences of reciprocal sums. [Chen, §9](https://hexagonmath.org/pdf/2611.01130v1)

The estimate $\log|E_K|\ll K\log\log K/\log K$ gives $|E_K|^2\le N^{1/2}$ for small enough $\eta$, since $\log K\sim\ell_2$ and $\log\log K\sim\ell_3$. Each $p>y>\sqrt N$ occurs only to the first power in $Q$. The smaller primes contribute at most $\pi(y)\log N=O(y)$. Hence $\log Q\ll y+K\sqrt N\ll N/K$. This proves the upper bound for every symmetric pair, and $B(N)=\ell_1\ell_2^{1+o(1)}$ gives the displayed scale. [Estimate for the number of distinct sums](largest-grid.md#size-of-the-largest-grid)

## How far must the cutoff grow to reflect a sum?

For $t\in E_N\cap[1/2,3/2]$, let $M(t)$ be the least $M\ge N$ for which $2-t\in E_M$, and let $R(N)$ be the maximum of $M(t)$ over these $t$. Then
$$
R(N)=N\log N\,(\log\log N)^{1+o(1)}.
$$
The same estimate holds for $M(t)$ whenever $\log\operatorname{den}(t)\ge bN$ for fixed $b>0$, where $\operatorname{den}$ is the reduced denominator. In particular this applies when $0<|1-t|\le e^{-bN}$, since $|1-t|\ge1/\operatorname{den}(t)$.

For the upper bound, use the construction at scale $x=\log N$. It gives a grid of denominator $G>2N$ on $[1/2,1]$ using denominators at most $H=\lceil C B(N)\rceil$. In particular $G\mid\Lambda_H$, by the grid point $(G-1)/G$. We claim that $M=NH$ covers every fraction $u\in[1/2,3/2]$ with denominator dividing $\Lambda_N$. [Construction at scale $x$](iterated-grid.md)

Write $u=1+h/\Lambda_M$ and apply the prime residue criterion. At each prime $p\le M$, let $q$ be its largest power at most $M$. If $q>N$, then $p\mid h$, and zero is always allowed. Otherwise $q\le N$ and $pq>M=NH$, so $p>H$. The grid fractions $s/G$ cover every residue modulo $p$, since $p\nmid G$ and $[G/2,G]$ contains at least $N\ge p$ consecutive integers. Multiplying their denominators by $q$ uses denominators at most $qH\le M$ and gives all possible numerator residues $(\Lambda_M/q)(s/G)$ modulo $p$. Every prime test passes, proving $R(N)\le NH$. [Prime residue criterion](prime-residues.md)

For the lower bound, $t$ and $2-t$ form a symmetric pair at $M=M(t)$. Its reduced offset denominator is $\operatorname{den}(t)$, so the sharp bound above gives
$$
bN\le \log\operatorname{den}(t)\ll
\frac{M\log_3 M}{\log M\log_2 M}.
$$
Since $N\le M\ll N B(N)$, this gives $M\gg_b N\ell_1\ell_2/\ell_3$, as claimed. To realize the worst-case scale, take $t=1+\sum_{N/2<p\le N}1/p$. The sum over primes is $o(1)$, and every one of those primes survives in the reduced denominator. The prime number theorem gives $\log\operatorname{den}(t)=(1/2+o(1))N$.

Examples on both sides can also lie within $\exp(-aN/B(N))$ of 1. Let $s=\sum_{N/2<p\le N}1/p$ and take the two grid points bracketing $1-s$ in the construction at $x=N/(CB(N))$. For large $N$ they lie in $[1/2,1]$, since $1/N\le s=o(1)$ and $D>N$. All prime factors of $D$ are at most $2x<N/2$. Adding $s$ to either point uses distinct denominators and retains every prime in $(N/2,N]$. Thus neither sum equals 1, both are within $1/D$ of it, and both have the asserted reflection delay. [Grid construction](iterated-grid.md)

## Which reduced denominators occur?

Let $L=\Lambda_N$. For each $p\le N$ prime let $C_p$ be the allowed residues of $h$ for $1+h/L$, and put $S_p=C_p\cap(-C_p)$. For sufficiently large $N$, the reduced denominators of the symmetric offsets $0<e\le1/2$ are exactly the divisors $d\ge2$ of
$$
D_{\rm sym}=L\bigg/\prod_{p:\,S_p=\{0\}}p .
$$
Indeed, both $1-h/L$ and $1+h/L$ occur precisely when $h\bmod p\in S_p$ for every $p$. Thus each prime in the product divides $h$, proving necessity. [Prime residue criterion](prime-residues.md)

Conversely, take $d\mid D_{\rm sym}$ with $d\ge2$ and put $b=L/d$. For each $p\mid d$ with $p\nmid b$, choose a nonzero class $r\bmod p$ such that $br\in S_p$ modulo $p$. Such a class exists by the definition of $D_{\rm sym}$. At the other primes dividing $d$, prescribe $r\equiv1$. The Chinese remainder theorem gives $r$ coprime to $d$ with $0<|r|\le(\prod_{p\mid d}p)/2\le d/2$. Every $p\mid L$ outside $d$ divides $b$, so $h=br$ passes every symmetric residue test. Hence $e=|r|/d$ works.
