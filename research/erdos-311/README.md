# Approximating 1 by sums of distinct unit fractions

Let $E_N$ consist of the sums $\sum_{n\in A}1/n$ over subsets $A\subseteq\{1,\ldots,N\}$, including the empty sum. Write $\delta(N)=\min_{u\in E_N,\ u\ne 1}|1-u|$. Erdős and Graham ask whether $-\log\delta(N)/N$ tends to a constant in $(0,1)$. [Problem #311](https://www.erdosproblems.com/311)

## Results on the individual gap

* For all sufficiently large $N$, one explicit congruence per prime $p\le N$ determines exactly which fractions in $[1/2,3/2]$ occur. Thus $L\delta(N)$ is the least nonzero absolute value of an admissible integer, where $L=\operatorname{lcm}(1,\ldots,N)$. Estimating this least integer on the exponential scale remains open. [Congruences and proof](prime-residues.md)
* Comparing three record errors gives $\liminf(-\log\delta(N))/N\le190/(73+\sqrt{25849})=0.81274298\ldots$. This implies $\delta(N)>e^{-0.813N}$ infinitely often without assuming a limiting rate. [Subsequence bound](record-gaps.md)
* For each $g(N)=o(N)$, the set of indices satisfying $L\delta(N)\le e^{g(N)}$ has natural density zero. An exact computation also excludes $L\delta(N)\le N^5$ throughout $1{,}000\le N\le1{,}000{,}000$. [Density proof and finite certificate](near-saturation.md)
* The exact minimum is certified for every $58\le N\le200$, including both a witness and an independent exclusion of smaller errors. The computations agree with the earlier table through 60 on their overlap. [Method and verification](exact-values.md) · [Exact values and witnesses](exact_gaps.tsv)

## Complete grids near 1

The congruences identify the largest denominator $D_*$ whose every grid point in $[1/2,3/2]$ occurs. Its size satisfies $\log D_*=N/(\log N\,(\log\log N)^{1+o(1)})$. The construction below gives the lower estimate for $\log D_*$ and the corresponding upper bound on $\delta(N)$. [Maximal denominator and size estimates](largest-grid.md)

**Upper bound.** Write $L_1(x)=\log x$ and $L_{j+1}(x)=\log L_j(x)$. There is an absolute $b>0$ such that for every sufficiently large $N$,
$$
\delta(N)\le
\exp\!\left(-\frac{bN}{L_1(N)L_2(N)L_3(N)^2}\right).
$$
In fact there is a common denominator $D$ with $\log D\ge bN/(L_1(N)L_2(N)L_3(N)^2)$ such that $s/D\in E_N$ for **every integer** $s$ between $D/2$ and $D$. Taking $s=D-1$ gives the stated distance to 1 from below. The construction gives no positive lower bound on $-\log\delta(N)/N$ independent of $N$.

## How to add primes to a common denominator

Suppose every integer $m$ with $aD\le m\le D$ has a representation of $m/D$ using distinct unit fractions whose denominators divide $D$ and are at most $B$. Here $0\le a<1$. Let $\mathcal P$ be a finite nonempty set of primes coprime to $D$, put $P=\prod_{p\in\mathcal P}p$, and suppose $[aD,D]$ contains at least $p$ integers for every $p\in\mathcal P$.

**Lemma.** Every fraction $s/(DP)$ with $s\in\mathbb Z$ and $a+\sum_{p\in\mathcal P}1/p\le s/(DP)\le 1$ has such a representation with denominators dividing $DP$ and bounded by $B\max\mathcal P$.

For each $p$ choose an integer $m_p\in[aD,D]$ satisfying
$$
m_p(P/p)\equiv s\pmod p .
$$
The multiplier $P/p$ is invertible modulo $p$, and the available consecutive integers cover every residue. Set
$$
m=\frac{s-\sum_{p\in\mathcal P} m_p(P/p)}{P}.
$$
The numerator vanishes modulo every prime dividing $P$, so $m$ is an integer. Moreover
$$
\frac{m}{D}=\frac{s}{DP}-\sum_{p\in\mathcal P}\frac{m_p}{pD}\in[a,1],
$$
because each subtracted term is between $0$ and $1/p$. Represent $m/D$ using the given denominators. For each $p$, represent $m_p/D$ in the same way and multiply its denominators by $p$. The resulting unit fractions sum to $s/(DP)$. Every denominator in the $p$ group contains $p$ and no other prime of $\mathcal P$. The unscaled group contains none of those primes. This proves distinctness across groups and both bounds on their denominators. $\square$

## Four applications

For a large real $x$, take all primes in $(x/2,x]$. The prime number theorem gives $\log P\sim x/2$, and $\sum_{x/2<p\le x}1/p\le 2\pi(x)/x=o(1)$. We use only $\log P\ge x/3$ and $\sum 1/p\le 1/8$ for all sufficiently large $x$.

1. Start with the least power of two $D_0\ge 2x+2$. Binary expansion represents every $m/D_0\in[0,1]$ with distinct denominators among $1,2,4,\ldots,D_0$. The lemma produces a denominator $D_1(x)=D_0P$ covering $[1/8,1]$, with denominators of its unit fractions bounded by $H_1(x)\le xD_0=O(x^2)$. Its largest prime factor is at most $x$, and $\log D_1(x)\ge x/3$.
2. To pass from stage $j$ to stage $j+1$, for $j=1,2,3$, take the stage-$j$ construction at $y=6\log x$. Its common denominator satisfies $D_j(y)\ge e^{y/3}=x^2$, and all its prime factors are at most $y<x/2$. The interval $[(j/8)D_j(y),D_j(y)]$ therefore contains at least $x$ integers. Apply the lemma with the primes in $(x/2,x]$. The new denominator $D_{j+1}(x)=D_j(y)P$ covers $[(j+1)/8,1]$, has no prime factor above $x$, and satisfies $\log D_{j+1}(x)\ge x/3$. The largest denominator of a unit fraction used is bounded by $H_{j+1}(x)\le xH_j(6\log x)$.

Substitution in the recurrence gives
$$
\begin{aligned}
H_2(x)&\ll x L_1(x)^2,\\
H_3(x)&\ll x L_1(x)L_2(x)^2,\\
H_4(x)&\ll x L_1(x)L_2(x)L_3(x)^2 .
\end{aligned}
$$
Take $x=cN/(L_1(N)L_2(N)L_3(N)^2)$ for a sufficiently small fixed $c>0$. Then $H_4(x)\le N$ for all sufficiently large $N$, the covered interval starts at $1/2$, and $\log D_4(x)\ge x/3$. This proves the upper bound with $b=c/3$.

## Why a grid cannot give the conjectured rate

Suppose all $s/D\in[1/2,1]$ belong to $E_N$, even allowing denominators that do not divide $D$. We show $\log D=O(N/\log N)$. We may assume $D>2N+2$. Representing $(D-1)/D$ shows $D\mid\operatorname{lcm}(1,\ldots,N)$.

Fix a prime $p\mid D$ with $p>\sqrt N$. Both $D$ and every multiple of $p$ up to $N$ have just one factor of $p$. Multiply a representation of $s/D$ by $p$ and reduce modulo $p$. Terms coming from denominators coprime to $p$ vanish. A denominator $pk$ contributes $1/k$ in the field of residues modulo $p$. The left side runs through every residue, since $D/p$ is invertible and $s$ runs through at least $p$ consecutive integers. Hence
$$
p\le 2^{\lfloor N/p\rfloor},\qquad p\log p\le N\log 2.
$$
In particular $p\le 2(\log 2)N/\log N$. These large primes together contribute $O(N/\log N)$ to $\log D$ by the prime number theorem. Primes at most $\sqrt N$ contribute at most $\sqrt N\log N$ altogether, since each prime power in $D$ is at most $N$. This proves the assertion. An individual fraction extremely close to 1 can exist without its neighboring grid points being representable. The unknown in #311 is the size of this individual gap.

## An exact reduction for the target 1

Let $S=cN/(L_1(N)^3L_2(N)^4)$ for a sufficiently small constant $c>0$, and set $Q=\operatorname{lcm}(1,\ldots,\lfloor S\rfloor)$. Every $m/Q\in[1/3,1]$ can be represented using distinct divisors of $Q$ at most $N$. This follows from the proof of Liu and Sawhney's Lemma 4.1. The prime-by-prime proof also gives an elementary derivation using the first grid construction. [Liu and Sawhney, Proposition 3.2 and Lemma 4.1](https://arxiv.org/html/2404.07113v1#S4) · [Elementary derivation](prime-residues.md)

Let $U=\{n\le N:n\nmid Q\}$, with $n$ positive, and write $R(B)=\sum_{n\in B}1/n$. For real $z$ define $d_*(z)=\min_{k\in\mathbb Z,\ k\ne z}|z-k|$, so $d_*(z)=1$ at integers. For all sufficiently large $N$,
$$
\delta(N)=\frac1Q\min_{B\subseteq U}d_*(Q R(B)).
$$
More generally the same right-hand side equals the minimum nonzero distance from $E_N$ to **any fixed rational $t\in(1/3,1]$**, once $N$ is sufficiently large in terms of $t$.

To see this, first observe $R(U)=o(1)$. Each member of $U$ is a multiple of some prime power $q>S$. Such multiples have total reciprocal sum bounded by $(1+\log(N/S))/q$. The primes $q\in(S,N]$ have reciprocal sum $O((1+\log(N/S))/\log S)$ by splitting into dyadic intervals and using $\pi(x)\ll x/\log x$. There are $O(\sqrt N\log N)$ higher prime powers at most $N$, each contributing at most $1/S$ to the sum of $1/q$ in this range. Since $N/S$ is polylogarithmic, these estimates give $R(U)=o(1)$. Also $Q/N\to\infty$ by the prime number theorem.

For large $N$, the fixed denominator of $t$ divides $Q$. Given $B\subseteq U$, any complementary contribution using divisors of $Q$ is an integer multiple of $1/Q$, so its nonzero distance to $t-R(B)$ is at least $d_*(Q R(B))/Q$. This distance is attainable. For nonempty $B$ we have $1/N\le R(B)\le o(1)$ uniformly, so $t-R(B)$ lies inside $[1/3,1]$ at distance at least $1/Q$ from both ends for large $N$. A nearest grid point giving a nonzero distance is in that interval and can be represented by Liu and Sawhney's lemma. Its denominators are disjoint from $B$. For empty $B$, use the grid point $t-1/Q$. Taking the minimum proves the formula.

Thus $\log Q=o(N)$, and deciding the positive exponential rate in #311 is equivalent to deciding it for the least nonzero distance in this last residue problem. A bound on the number of possible residues alone does not bound how close one of them can lie to an integer. [Sawin's discussion of counting distinct sums](https://www.erdosproblems.com/forum/thread/311)

## Numerical replay and prior work

The Python 3.10+ verifier constructs the sums by the lemma and checks their value using independent rational addition. It exhausts the 89 covered numerators for $D=560$, then checks the endpoints and $1-1/373520$ after a second application. The asymptotic estimate follows from the proof above. [Verifier](verify_grid.py)

~~~sh
python3 research/erdos-311/verify_grid.py
~~~

Tang's January 2026 note gives $\delta(N)\le\exp(-cN/[(\log N)^3(\log\log N)^3])$. The bound above gives a larger guaranteed exponent. Related constructions include Bleicher and Erdős's interval of divisor sums, Liu and Sawhney's representation of all numerators in an interval for smooth denominators, and Chen's covering of residues at almost all primes. These results address closely related questions, and priority for the bound above has not been established. [Tang, Theorem 4.1](https://github.com/QuanyuTang/erdos-problem-311-note) · [Bleicher and Erdős, Lemma 4](https://users.renyi.hu/~p_erdos/1976-10.pdf) · [Liu and Sawhney, Lemma 4.1](https://arxiv.org/html/2404.07113v1#S4) · [Chen, Lemma 13](https://hexagonmath.org/pdf/2611.01130v1)
