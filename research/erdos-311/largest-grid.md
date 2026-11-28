# The largest complete grid near 1

Call an integer $D\ge1$ admissible if every $s/D\in[1/2,3/2]$ with integer $s$ is a sum of distinct reciprocals from $1,1/2,\ldots,1/N$. Write $L=\operatorname{lcm}(1,\ldots,N)$ and let $C_p$ be the allowable numerator residues at $p$ from the [prime criterion](prime-residues.md). For all sufficiently large $N$ put
$$
D_* = \frac{L}{\prod_{p\le N:\,C_p\ne\mathbb F_p}p}.
$$
Then **$D$ is admissible if and only if $D\mid D_*$**. With $L_j$ denoting the $j$th iterated natural logarithm evaluated at $N$,
$$
\frac{N}{L_1L_2L_3^2}\ll \log D_* \ll \frac{N L_3}{L_1L_2}.
$$
In particular $\log D_*=N/(L_1L_2^{1+o(1)})$. This leaves a factor of order at most $L_3^3$ between the two bounds.

## Exact maximality

For a grid point of $D_*$ write $s/D_*=1+h/L$. Then $h=(s-D_*)L/D_*$ vanishes modulo every prime whose residue set is proper. Zero is always admissible. All remaining prime conditions hold for every residue. The prime criterion realizes the grid point. Every divisor of $D_*$ gives a subgrid.

Conversely suppose the grid of $D\ge2$ is attainable. Its point $(D-1)/D$ has reduced denominator $D$, so $D\mid L$. Fix a prime $p\le N$ for which $p\nmid L/D$. Then $p\mid D$, and the offsets $h=(s-D)L/D$ run through all residues modulo $p$ as $s$ runs through the integers in $[D/2,3D/2]$. There are at least $D\ge p$ consecutive choices. Necessity in the prime criterion forces $C_p=\mathbb F_p$. Hence each prime with a proper residue set divides $L/D$, proving $D\mid D_*$. The case $D=1$ is immediate.

## Size of the largest grid

The [four-stage construction](README.md#four-applications) produces a denominator $D_4$ with $\log D_4\gg N/(L_1L_2L_3^2)$ and represents its grid in $[1/2,1]$. This shorter interval still contains at least $N$ consecutive numerators for sufficiently large $N$, since $D_4/N\to\infty$. The necessity argument above applies to every prime up to $N$, showing $D_4\mid D_*$. This gives the lower bound.

For the upper bound let $E_k$ denote the set of distinct reciprocal subset sums using denominators at most $k$. We first give an elementary estimate
$$
\log |E_k|\ll \frac{k\log\log k}{\log k}
$$
for large $k$. Put $y=k/\log k$ and $Q=\operatorname{lcm}(1,\ldots,\lfloor y\rfloor)$. Denominators dividing $Q$ give at most $1+Q(1+\log k)$ values, whose logarithm is $O(k/\log k)$. Each remaining denominator is a multiple of a prime power $q\in(y,k]$. The number of such denominators is at most
$$
k\sum_{y<p\le k}\frac1p+
k\sum_{y<p^a\le k,\;a\ge2}\frac1{p^a}.
$$
Divide $(y,k]$ into $O(\log\log k)$ dyadic intervals. By $\pi(x)\ll x/\log x$ and $\log y\asymp\log k$, each interval contributes $O(1/\log k)$ to the first sum before multiplication by $k$. There are $O(\sqrt{k}\log k)$ higher prime powers at most $k$, each contributing at most $1/y$ to the second sum. The total number of remaining denominators is $O(k\log\log k/\log k)$. Each gives two choices, proving the estimate.

Let $T=CNL_3/(L_1L_2)$, with $C$ a sufficiently large absolute constant. For $p>T$ one has $p>\sqrt N$, so $q_p=p$ and $k_p=\lfloor N/p\rfloor\le K=\lfloor L_1L_2/(C L_3)\rfloor$. Reduction modulo $p$ of $E_{k_p}$ and multiplication by $L/p$ give $C_p$. Monotonicity and the estimate just proved yield
$$
\log |C_p|\le\log |E_K|\ll K\frac{\log\log K}{\log K}
\le \frac{O(1)}{C}\log N .
$$
Here $\log K\sim L_2$ and $\log\log K\sim L_3$ for fixed $C$. As $\log T\sim\log N$, it follows that $|C_p|<p$ for every $p>T$. All those primes occur to exponent one in $L$ and disappear from $D_*$. The remaining possible contributions to $\log D_*$ are bounded by $\sum_{p\le T}\log p=O(T)$ and $O(\sqrt N\log N)$ for the extra exponents of primes at most $\sqrt N$. This proves the upper bound.

In particular a complete grid gives an error $1/D_*$ at 1. An isolated point from another residue class can give a smaller error. Estimating that improvement is the remaining issue in problem #311.
