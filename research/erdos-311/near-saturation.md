# When an individual reciprocal sum approaches the LCM bound

Put $L_n=\operatorname{lcm}(1,\ldots,n)$ and $h_n=L_n\delta(n)$. Thus $h_n$ is a positive integer. For any function $g(n)=o(n)$,
$$
\#\{n\le X:h_n\le\exp(g(n))\}=o(X).
$$
In particular, $\delta(n)=1/L_n$ can hold only on a set of natural density zero. For every fixed $K\ge0$ a prime-gap bound sharpens the count to
$$
\#\{n\le X:h_n\le n^K\}=O_K(X^{0.525}).
$$
Separately, the finite calculation below gives $h_n>n^5$ at every $n$ from $1{,}000$ to $1{,}000{,}000$, inclusive. Neither counting statement excludes infinitely many exceptions.

## A divisibility condition at two indices

For each $n$, fix a subset $A_n\subseteq\{1,\ldots,n\}$ attaining the minimum, and let $a_n=L_n(\sum_{j\in A_n}1/j-1)$. Thus $|a_n|=h_n$. Take $n\le m<2n$ and write $R=L_m/L_n$, $a=a_n$, $b=a_m$. Then
$$
\prod_{m/2<p\le n}p\ \mid\ ab(Ra-b),
$$
where the product runs over primes. For each such $p$, its only positive multiple up to $m$ is $p$ itself. Modulo $p$, the numerator $a$ is either zero or $L_n/p$, according as $p$ is omitted or selected. The choices for $b$ are zero and $L_m/p$. If $p$ divides neither numerator, it divides $Ra-b$. This proves the divisibility. Sawin used the same top-interval prime observation to study adjacent changes of the minimum in the #311 discussion. [Sawin’s comments, July 2026](https://www.erdosproblems.com/forum/thread/311)

Write $\theta(t)=\sum_{p\le t}\log p$ and $\psi(t)=\log L_{\lfloor t\rfloor}$. The prime number theorem gives $\theta(t)=t+o(t)$ and $\psi(t)=t+o(t)$. For $n\le m<2n$ and $Ra\ne b$, taking logarithms gives
$$
\theta(n)-\theta(m/2)\le \log|ab|+\log(R|a|+|b|).
$$
If $\log|a|=o(n)$ and $\log|b|=o(m)$, the right side is at most $m-n+o(n)$, because $\log R=\psi(m)-\psi(n)=m-n+o(n)$. Consequently distinct signed minimizing errors at two such indices require $m\ge(4/3-o(1))n$. If $Ra=b$, the errors coincide and $\log R\le\log|b|=o(n)$ gives $m=n+o(n)$.

## Counting the exceptional indices

Fix $g(n)=o(n)$ and call an index exceptional when $\log h_n\le g(n)$. In any sufficiently large interval $[Y,5Y/4]$, every exceptional index has the same signed minimizing error. Indeed, distinct errors require a ratio at least $4/3-o(1)$, strictly larger than $5/4$. The error estimates are uniform in the interval since the prime number theorem and $g(t)=o(t)$ hold on the entire tail. When the interval contains two or more exceptional indices, let $n$ and $m$ be the least and greatest. Their errors coincide, so $m-n=o(Y)$. Thus there are $o(Y)$ exceptional indices in the interval. Partition $[1,X]$ into consecutive intervals with endpoints $X(4/5)^j$. Their lengths sum geometrically, giving $o(X)$ exceptions in total.

When $h_n\le n^K$ and $h_m\le m^K$, equality of signed errors gives $R=|b|/|a|\le m^K$. Every prime $p\in(n,m]$ divides $R$, so at most $K\log m/\log n=O_K(1)$ primes lie there. Baker, Harman and Pintz proved that $[t-t^{0.525},t]$ contains a prime for all sufficiently large $t$. Thus within $[Y,5Y/4]$ any stretch with no primes has length $O(Y^{0.525})$, and $m-n=O_K(Y^{0.525})$. Summing the geometric intervals gives $O_K(X^{0.525})$. [Baker, Harman and Pintz, Theorem 1](https://doi.org/10.1112/plms/83.3.532)

## How long the minimum must stay constant

Suppose $n<m<2n$ and $\delta(m)<\delta(n)$. Then $Ra\ne b$ and $|b|\le R|a|$ by monotonicity. The divisibility condition implies
$$
\theta(n)-\theta(m/2)\le\log 2+2\log R+3\log|a|.
$$
Writing $u_n=-\log\delta(n)$ and $\log |a|=\psi(n)-u_n$ gives $m\ge(6/5)u_n-o(n)$. In particular, along any sequence with $h_n=\exp(o(n))$, for each fixed $0<\eta<1/5$ and all sufficiently large indices in the sequence,
$$
\delta(m)=\delta(n)\qquad\text{for every integer }n\le m\le(6/5-\eta)n.
$$
The conclusions concern approximations close to the extremal scale $\exp(-(1+o(1))n)$. A rate $\delta(n)=\exp(-(c+o(1))n)$ for $0<c<1$ would instead give $\log h_n=(1-c+o(1))n$. The density-zero theorem alone therefore leaves #311 open.

## Finite certificate by residues

For every integer $1{,}000\le n\le1{,}000{,}000$ the verifier proves $L_n\delta(n)>n^5$. Starting at $u=1{,}000$, it uses consecutive blocks $[u,v]$, where $v$ is the smaller of $\lfloor3u/2\rfloor$ and $1{,}000{,}000$. The seven greatest primes at most $u$ all exceed $v/2$, a condition the verifier checks. Let $T$ be those primes and $P$ their product. For any subset $A\subseteq[1,n]$ the signed numerator of its error obeys
$$
L_n\left(\sum_{j\in A}1/j-1\right)
\equiv \frac{L_n}{P}\sum_{p\in A\cap T}\frac{P}{p}\pmod P .
$$
Indeed $P$ divides $L_n/j$ unless $j$ is one of the seven primes. The $128$ choices of $A\cap T$ cover every possible residue. For the empty choice, a nonzero signed numerator has magnitude at least $P$. For each nonempty choice the program takes its representative $0\le r<P$ and checks $\min(r,P-r)>w^5$, where $w$ is the last index of the current segment with unchanged $L_n$. The empty choice separately passes $P>w^5$. This rules out every nonzero numerator of magnitude at most $n^5$ throughout the segment.

The program generates all prime powers in order. At a power of $p$, $L_n$ acquires exactly one additional factor of $p$. It uses these updates to maintain $L_n/P$ modulo $P$ and checks the initial residue at $1{,}000$ against the direct integer LCM. The run covers 999,001 indices in 18 blocks and 78,555 constant-LCM segments, including splits at block boundaries. [Verifier](saturation_sieve.py)

~~~sh
python3 research/erdos-311/saturation_sieve.py
~~~
