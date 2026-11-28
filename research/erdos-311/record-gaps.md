# A lower bound on the error along a subsequence

Let $\delta(N)$ be the least nonzero distance from 1 to a sum of distinct reciprocals with denominators at most $N$. Then
$$
\sigma:=\liminf_{N\to\infty}\frac{-\log\delta(N)}N
\le \frac{190}{73+\sqrt{25849}}=0.8127429817\ldots .
$$
In particular $\delta(N)>e^{-0.813N}$ infinitely often. The argument extends Will Sawin's two-error bound of $5/6$. His bound of about $0.69$ assumes the limiting rate exists. [Sawin's discussion](https://www.erdosproblems.com/forum/thread/311)

**Counting rule.** If two distinct integers agree modulo $p$, their difference is a nonzero multiple of $p$. Thus if $m$ pairs in a list of distinct integers agree modulo $p$, the product of all pairwise differences is divisible by $p^m$.

**Choose three errors.** Start at $n_1=1$. Let $n_{j+1}$ be the first index at which the minimum falls below $\delta(n_j)/4$. Such indices exist because $1/2+\cdots+1/2^k=1-2^{-k}$, where the sum uses powers of two. Write $u_j$ for a signed error attaining $\delta(n_j)$ and $H_j=-\log|u_j|$. Since $\delta(n_{j+1}-1)\ge\delta(n_j)/4$,
$$
H_j\ge(\sigma-o(1))n_{j+1}.
$$
We may assume $\sigma>4/5$. Put $X=n_j$, $U=n_{j-1}$ and $L=\operatorname{lcm}(1,\ldots,X)$. Then
$$
(x,y,z)=L(u_{j-2},u_{j-1},u_j)
$$
are integers with $|x|>4|y|$ and $|y|>4|z|>0$. We use the prime number theorem in the forms $\log L=X+o(X)$ and $\sum_{p\le t}\log p=t+o(t)$.

**Count with two errors.** For $X/2<p\le X$, the only available denominator divisible by $p$ is $p$. Each of $y,z$ is therefore either $0$ or $L/p$ modulo $p$. Among $0,y,z$ two must agree. Hence the product of these primes divides $yz(y-z)$, whose absolute value is at most $2L^3e^{-2H_{j-1}-H_j}$. Taking logs gives
$$
H_j+2H_{j-1}\le(5/2+o(1))X.
$$
It follows that $r=\limsup_j n_{j+1}/n_j$ is finite and $\sigma(r+2)\le5/2$. In particular $1\le r\le9/8$.

**Count with three errors.** Take the six integers
$$
x,\quad y,\quad z,\quad x+y,\quad x+z,\quad y+z.
$$
They are distinct because the largest term in any difference outweighs the others. Let $V$ be the absolute product of their fifteen pairwise differences. Three sums contain $x$ and three omit it, giving nine cross pairs. Of the remaining six pairs, four first differ at $y$ and two differ only at $z$. Each difference is at most twice its largest term in absolute value. Thus
$$
\log V\le15\log(2L)-9H_{j-2}-4H_{j-1}-2H_j.
$$

* For $X/2<p\le X$, divide the residues of $x,y,z$ by $L/p$ modulo $p$ to get labels in $\{0,1\}$. At least six pairs of the six sums agree. With one or three ones there are two groups of three equal sums. With two ones, four sums equal 1. With no ones all six agree.
* For $X/3<p\le X/2$, the available multiples are $p,2p$. Dividing by $L/(2p)$ gives labels in $\{0,1,2,3\}$. A zero can be added to either other label without changing it. Two equal labels also stay equal after adding the third. Either case gives two equal pairs. Otherwise the labels are $1,2,3$, and $1+2=3$ gives one pair. When also $p>U/2$, the two older labels are in $\{0,2\}$, guaranteeing a zero or a repetition.

Since $U/X\ge1/r-o(1)$, eventually $U/2>X/3$. The counting rule and the prime number theorem give
$$
\log V\ge 6(X/2)+X/6+(X-U)/2+o(X).
$$
Comparing the two bounds on $V$ yields
$$
2H_j+4H_{j-1}+9H_{j-2}\le (34/3)X+U/2+o(X).
$$

**Read off the constant.** Take indices with $n_{j+1}/X\to r$. Substitute $H_i\ge(\sigma-o(1))n_{i+1}$ in the last inequality and use $U/X\ge1/r-o(1)$ with $9\sigma-1/2>0$. This gives $2\sigma r+4\sigma+(9\sigma-1/2)/r\le34/3$. Together with the two-error bound,
$$
\sigma\le\min\!\left\{\frac5{2r+4},\ \frac{68r+3}{12r^2+24r+54}\right\}.
$$
On $[1,9/8]$ the first fraction decreases and the second increases (its derivative has the sign of $150-3r-34r^2$). Their minimum is largest where they cross, at $38r^2+79r-129=0$. Their common value is the positive root of $54c^2+73c=95$, namely $190/(73+\sqrt{25849})$.
