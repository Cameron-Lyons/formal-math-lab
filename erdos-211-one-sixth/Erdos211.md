# Erdős Problem 211: the constant 1/6 in Beck's theorem fails

## The result

Take a finite set of $n$ points in the plane and draw every straight line passing through at least two of them — we call such a line *determined* by the point set. If all $n$ points lie on one line, they determine only $1$ line; if they are in general position (no three collinear), they determine $\binom{n}{2} \approx \frac{1}{2}n^2$ lines. What happens in between?

In 1983, Beck, and independently Szemerédi and Trotter, proved a celebrated dichotomy: there is an absolute constant $c>0$ such that for all $1\le k<n$, every set of $n$ points with at most $n-k$ on any single line determines at least $ckn$ lines. In 1984, Erdős wondered whether $c=1/6$ works and suggested looking for a counterexample first.

We give one: there are arbitrarily large sets of $n$ points, with only $O(n^{2/3})$ on any line, that determine at most $0.166\,n^2$ lines. Thus $c=1/6$ fails, even if we ask for the bound only for large $n$ and weaken it by a factor of $1-\varepsilon$. Beck's theorem itself is unaffected. Our theorem contradicts $kn/6$ only when $k$ is close to $n$: above about $0.996\,n$ (or above about $0.96\,n$ with the sharper constant in Remark 2). We claim nothing for smaller $k$.

**Theorem.** Let $M\ge 1000$ be an integer and set $R=30030M$. There is a set $P$ of $n\ge 3R^3$ points in the plane such that every line contains at most $2R^2$ points of $P$, and $P$ determines at most $0.166\,kn$ lines, where $k=n-2R^2$.

**Corollary.** It is false that for every $\varepsilon>0$ there exists an integer $N\ge 1$ such that, for all $n\ge N$ and $1\le k<n$, every set of $n$ points with at most $n-k$ on any line determines at least $(1-\varepsilon)kn/6$ lines.

*Proof of the corollary.* Suppose the statement holds. Pick the integer $N$ corresponding to $\varepsilon=1/1000$, and apply the Theorem with $M=\max(1000,N)$. Then $n\ge 3R^3\ge R\ge N$ and $n>2R^2>0$, so $1\le k<n$, and every line contains at most $2R^2=n-k$ points. By assumption $P$ would determine at least $\frac{999}{6000}kn=0.1665\,kn>0.166\,kn$ lines, a contradiction. $\square$

## The idea

To beat $n^2/6$, we want a point set with many rich collinearities (so many pairs of points collapse onto the same line), yet no single line holding a positive fraction of the points. A natural candidate comes from projective geometry: project a 3D integer box onto a plane.

Let $S$ be the box of integer vectors $(x,y,z)$ in $[-R,R-1]^2\times[1,R-1]$, and project each vector onto the horizontal plane $z=1$ via $(x,y,z) \mapsto (x/z, y/z)$ to obtain our planar point set $P$. Think of each vector $v \in S$ as defining a ray from the origin in $\mathbb{R}^3$; its projection $\pi(v)$ is where that ray pierces $z=1$.

1. **Counting points (about $4R^3/\zeta(3)$).** There are about $4R^3$ integer vectors in $S$. Call a vector *primitive* if its coordinates are coprime (no prime divides all three). Distinct primitive vectors lie on distinct rays and therefore give distinct points of $P$, while dividing any vector in $S$ by the gcd of its coordinates produces a primitive vector in $S$ with the same projection. For a random integer triple, the probability that no prime $p$ divides all three entries is $\prod_p (1 - p^{-3}) = 1/\zeta(3)$ (where $\zeta(s) = \sum_{m=1}^\infty m^{-s}$ is the Riemann zeta function), so $P$ has about $4R^3/\zeta(3)$ points.

2. **Charging lines to height-minimal spanning pairs.** Two vectors $u, w \in S$ with distinct projections span a 2D plane through the origin in $\mathbb{R}^3$, which slices $z=1$ in a determined line of $P$. Rather than counting all pairs $(u,w)$, we pick *one* canonical spanning pair for each determined line: a pair $(u,w)$ minimizing the sum of third coordinates ("heights") $z(u) + z(w)$, ordered so that $z(u) \ge z(w)$. Pairs with equal heights $z(u) = z(w)$ number only $O(R^5)$ and are negligible. For every remaining line, $z(u) > z(w)$, and minimality imposes two strong constraints:
   * **The subtraction test (far pairs):** The difference $u - w$ lies in the same 2D plane and has strictly smaller positive height $z(u) - z(w) < z(u)$, so it *cannot* lie inside the box $S$ (otherwise it could replace $u$). Hence $u$ and $w$ must differ by at least $R$ in $x$ or in $y$. For two random integers in $[-R, R-1]$, the event $|a - b| < R$ has probability about $3/4$ (visualize the $2R \times 2R$ square minus two corner triangles of leg $R$); failing in $x$ or in $y$ leaves only a fraction $1 - (3/4)^2 = 7/16$ of all pairs.
   * **The prime-divisibility test (independence mod $p$):** The vectors $u$ and $w$ must be linearly independent modulo every prime $p$; otherwise some integer combination $(au + bw)/p$ would lie in $S$ with smaller height and replace one of them. For a random pair of vectors in $\mathbb{F}_p^3$, being linearly independent means the first is nonzero (probability $1 - p^{-3}$) and the second is not one of its $p$ scalar multiples (probability $1 - p^{-2}$). Multiplying over all primes gives $1/(\zeta(2)\zeta(3))$.

3. **Why the ratio beats $1/6$.** Since roughly $\frac{1}{2}(4R^3)^2$ pairs satisfy $z(u) > z(w)$, the number of determined lines is at most about
   $$\frac{1}{2}\cdot\frac{7}{16}\cdot\frac{(4R^3)^2}{\zeta(2)\zeta(3)}\approx 1.770\,R^6,\qquad\text{while}\qquad
   \Bigl(\frac{4R^3}{\zeta(3)}\Bigr)^2\approx 11.07\,R^6.$$
   Their ratio is about $0.1599 < 1/6 \approx 0.1667$. That margin is comfortable enough that our formal proof needs only the first six primes ($2, 3, 5, 7, 11, 13$) to bound the lines, and an elementary union bound (no Möbius inversion) to lower-bound the points.

## Notation

Throughout, $R\ge 1$ is an integer and
$$S=\{v=(x,y,z)\in\mathbb{Z}^3:\ -R\le x\le R-1,\ -R\le y\le R-1,\ 1\le z\le R-1\}.$$
We write $x(v),y(v),z(v)$ for the coordinates of $v$ and call $z(v)$ the *height* of $v$. For a vector $v$ of positive height, set $\pi(v)=(x(v)/z(v),\,y(v)/z(v))$. Let $P=\pi(S)$, $n=|P|$, and let $L$ be the number of lines determined by $P$. The letter $p$ always stands for a prime.

A pair $(u,w)$ of vectors in $S$ is:

* a *spanning pair* of a line $\ell$ if $\pi(u)\ne\pi(w)$ and both points lie on $\ell$;
* *far* if $|x(u)-x(w)|\ge R$ or $|y(u)-y(w)|\ge R$;
* *good at* $p$ if $u$ and $w$ are linearly independent modulo $p$, as vectors in $\mathbb{F}_p^3$.

## Few lines

The first three lemmas establish the algebraic replacement moves and prove that every determined line (with unequal-height minimal spanning pair) is witnessed by a pair that is both *far* and *good at every prime*. Lemmas 4–6 then count how many such pairs can exist.

**Lemma 1 (combinations).** *Why we need this:* It translates linear combinations in $\mathbb{R}^3$ into collinearity in the plane, telling us when a new vector $v$ can replace $u$ or $w$ in a spanning pair.

Let $u,w,v$ be integer vectors of positive height with $\pi(u)\ne\pi(w)$, and suppose $mv=au+bw$ for integers $m\ge 1$, $a$, and $b\ne 0$. Then $\pi(v)\ne\pi(u)$, and $\pi(v)$ lies on the line through $\pi(u)$ and $\pi(w)$.

*Proof.* Set $t=\dfrac{b\,z(w)}{m\,z(v)}\ne 0$. Since $m\,z(v)=a\,z(u)+b\,z(w)$, we have $\dfrac{a\,z(u)}{m\,z(v)}=1-t$. Therefore
$$\frac{x(v)}{z(v)}=\frac{a\,x(u)+b\,x(w)}{m\,z(v)}=(1-t)\frac{x(u)}{z(u)}+t\,\frac{x(w)}{z(w)},$$
and the same identity holds for $y$. Thus $\pi(v)=(1-t)\pi(u)+t\,\pi(w)$ with $t\ne 0$. $\square$

In particular, if $(u,w)$ spans $\ell$ and $v\in S$ satisfies $mv=au+bw$ with $m\ge 1$, then $(u,v)$ spans $\ell$ whenever $b\ne 0$ ("$v$ can replace $w$"), and $(v,w)$ spans $\ell$ whenever $a\ne 0$ ("$v$ can replace $u$").

**Lemma 2 (convexity).** *Why we need this:* When we divide a non-negative integer combination $au + bw$ by a prime $p$ in Lemma 3, we must know that the resulting integer vector $v = (au+bw)/p$ stays inside the box $S$.

Let $u,w\in S$ and $mv=au+bw$ with $v\in\mathbb{Z}^3$ and integers $a,b\ge 0$ satisfying $1\le a+b\le m$. Then $v\in S$.

*Proof.* Because $R-1\ge 0$ and $0 \le a+b \le m$, each $x$-coordinate bound scales safely:
$$-mR \le -(a+b)R \le a\,x(u) + b\,x(w) = m\,x(v) \le (a+b)(R-1) \le m(R-1),$$
and the exact same bounds hold for $y(v)$. Similarly $m\,z(v)\le (a+b)(R-1) \le m(R-1)$. Finally, since $a, b \ge 0$ are not both $0$ and $z(u), z(w) \ge 1$, we have $m\,z(v)=a\,z(u)+b\,z(w)>0$, so the integer $z(v)$ is at least $1$. Thus $v \in S$. $\square$

**Lemma 3 (short pairs).** *Why we need this:* This is the geometric heart of the line bound. Picking a height-minimal spanning pair for each line automatically enforces both the *far* condition and linear independence modulo every prime.

Every determined line has a spanning pair $(u,w)$ that either satisfies $z(u)=z(w)$, or satisfies $z(u)>z(w)$ and is both far and good at every prime.

*Proof.* Among all spanning pairs of the line, choose $(u,w)$ minimizing $z(u)+z(w)$. Swapping $u$ and $w$ if needed, we may assume $z(u)\ge z(w)$. If $z(u)=z(w)$ we are done, so suppose $z(u)>z(w)$.

*Step 1: $(u,w)$ is far.* Suppose to the contrary that $(u,w)$ is not far. Then $v=u-w$ satisfies $|x(v)|,|y(v)|\le R-1$ and $1\le z(v)=z(u)-z(w)\le R-1$, so $v\in S$. By Lemma 1 (with $m=1, a=1, b=-1$), $v$ can replace $u$. Yet $z(v)+z(w)=z(u)<z(u)+z(w)$, contradicting minimality.

*Step 2: $(u,w)$ is good at every prime $p$.* Suppose $u$ and $w$ are linearly dependent modulo $p$. Then there exist integers $a,b\in[0,p-1]$, not both $0$, such that $au+bw=pv$ for some $v\in\mathbb{Z}^3$.

To apply Lemma 2, we need $a + b \le p$. If $a+b>p$, then necessarily $a,b\ge 1$, and flipping to $(a', b', v') = (p-a,\,p-b,\,u+w-v)$ still satisfies $a'u + b'w = pv'$ with $a',b'\in[1,p-1]$, while now $a'+b' = 2p - (a+b) < p$. Thus we may assume $1\le a+b\le p$, and Lemma 2 gives $v\in S$. Now split on whether $a = 0$:

* If $a=0$, then $b\ge 1$, so by Lemma 1, $v$ can replace $w$. Yet $z(v)=\frac{b}{p}\,z(w)<z(w)$ since $b < p$, contradicting minimality.
* If $a>0$, then by Lemma 1, $v$ can replace $u$. Yet $p\,z(v)=a\,z(u)+b\,z(w)<p\,z(u)$: if $b=0$ this holds because $a<p$, and if $b>0$ it holds because $z(w)<z(u)$ and $a+b\le p$. Dividing by $p$ gives $z(v) < z(u)$, again contradicting minimality. $\square$

**Lemma 4 (far blocks).** *Why we need this:* In Lemma 5 we will divide every coordinate by $Q = 30030$ and keep track of its integer quotient in $[-M, M)$. This lemma is the exact discrete counterpart of the $3/4$-versus-$7/16$ area calculation for those quotients.

Let $M\ge 1$ be an integer, and write $[-M,M)$ for the set of integers $i$ with $-M\le i<M$.

1. There are $M(M+1)/2$ integer pairs $(i,j)$ with $0\le i\le j<M$.
2. Call $(i,j)\in[-M,M)^2$ *near* if $|i-j|<M$. There are at least $3M^2-M$ near pairs.
3. There are at most $7M^3(M+1)$ *far blocks*, meaning pairs $(q,q')$ in $([-M,M)^2)^2$ where at least one of $q,q'$ is not near.

*Proof.*
(1) Counting $i \in \{0, \dots, j\}$ for each $j \in \{0, \dots, M-1\}$ gives $\sum_{j=0}^{M-1}(j+1) = M(M+1)/2$.

(2) Let $(i,j)\in[-M,M)^2$ fail to be near, so $|i-j|\ge M$.
* If $j\ge i+M$, then $0\le i+M\le j<M$, so $(i+M,j)$ is one of the pairs in (1) and uniquely determines $(i,j)$.
* Otherwise $i\ge j+M$, and $(j+M,i)$ is one of the pairs in (1).

Thus at most $2 \cdot M(M+1)/2 = M(M+1)$ pairs are not near, leaving at least $4M^2-M(M+1)=3M^2-M$ near pairs.

(3) Out of all $(4M^2)^2 = 16M^4$ pairs $(q,q')$, part (2) implies that both $q$ and $q'$ are near in at least $(3M^2-M)^2$ of them. The number of far blocks is therefore at most
$$16M^4-(3M^2-M)^2=7M^4+6M^3-M^2\le 7M^3(M+1).\qquad\square$$

From now on let $M\ge 1$ be an integer, $Q=30030=2\cdot 3\cdot 5\cdot 7\cdot 11\cdot 13$, $R=QM$, and
$$G=\prod_{p\in\{2,3,5,7,11,13\}}(p^3-1)(p^3-p).$$

**Lemma 5 (far pairs).** *Why we need this:* Splitting each coordinate $t$ into its *coarse quotient* $\lfloor t/Q \rfloor$ and its *fine residue* $t \bmod Q$ decouples our two filters completely: the *far* condition restricts the coarse quotients (Lemma 4), while linear independence modulo the six primes restricts the fine residues independently!

Let $A$ be the number of pairs $(u,w)$ in $S\times S$ with $z(u)>z(w)$ that are far and good at the six primes $2,3,5,7,11,13$. Then
$$A\le 7M^3(M+1)\cdot\frac{M(M+1)}{2}\cdot G.$$

*Proof.* Map each such pair $(u,w)$ to its residues modulo the six primes $2,3,5,7,11,13$ together with the quotients $\lfloor\cdot/Q\rfloor$ of its six coordinates. By the Chinese remainder theorem, the residues modulo these six distinct primes determine $(u,w)$ modulo $Q$; together with the quotients $\lfloor \cdot / Q \rfloor$, they reconstruct $(u,w)$ uniquely. We bound the number of possibilities for each component:

* *Residues modulo $p$.* For each $p \in \{2,3,5,7,11,13\}$, the reduced pair is linearly independent in $\mathbb{F}_p^3$. There are $(p^3-1)(p^3-p)$ independent pairs: the first vector can be any of the $p^3-1$ nonzero vectors, and the second can be any vector other than its $p$ scalar multiples. Multiplying over the six primes gives $G$ choices.
* *Quotients of $z(w)$ and $z(u)$.* Call them $i$ and $j$. Since $0<z(w)<z(u)<QM$, we have $0\le i\le j<M$. By Lemma 4(1) there are $M(M+1)/2$ choices.
* *Quotients of the $x$ and $y$ coordinates.* The quotients of $x(u),x(w)$ form a pair $(i,i')\in[-M,M)^2$, and those of $y(u),y(w)$ form another. Observe that if $|i-i'|\le M-1$, then the difference of remainders can add at most $Q-1$, so
  $$|x(u)-x(w)|\le Q(M-1)+(Q-1)=QM-1=R-1,$$
  and the same holds for $y$. Since $(u,w)$ is far, at least one of these two quotient pairs is not near, so together they form a far block. By Lemma 4(3) there are at most $7M^3(M+1)$ choices.

Multiplying the three counts gives the stated bound on $A$. $\square$

**Lemma 6 (few lines).** *Why we need this:* Combines Lemma 3 and Lemma 5 with the small $O(R^5)$ count of equal-height pairs and evaluates the explicit six-prime product.

$L\le 1.8008\,R^4(R+30030)^2+16R^5$.

*Proof.* Every spanning pair determines a unique line, so Lemma 3 gives $L\le A+B$, where $B$ is the number of pairs $(u,w)\in S\times S$ with $z(u)=z(w)$. Once $u \in S$ is chosen (at most $4R^3$ choices), $z(w) = z(u)$ is fixed, leaving $(2R)^2$ choices for $(x(w), y(w))$; thus $B\le |S|\cdot(2R)^2\le 4R^3\cdot 4R^2=16R^5$.

For the six-prime density factor,
$$\frac{G}{Q^6}=\prod_{p\in\{2,3,5,7,11,13\}}\Bigl(1-\frac{1}{p^2}\Bigr)\Bigl(1-\frac{1}{p^3}\Bigr)<
0.65625\cdot 0.855968\cdot 0.95232\cdot 0.976736\cdot 0.990991\cdot 0.993631<0.5145,$$
and $Q^6M^4(M+1)^2=R^4(R+Q)^2$. Substituting into Lemma 5 gives
$$A\le \frac{7}{2}\cdot 0.5145\,R^4(R+Q)^2\le 1.8008\,R^4(R+Q)^2,$$
and adding $B \le 16R^5$ completes the proof. $\square$

## Many points

To show $L \le 0.166\,kn$, we also need a clean lower bound on the number of projected points $n = |P|$. Rather than computing the exact Möbius-inversion count of primitive vectors, a direct union bound over all primes $p < R$ already captures more than $3.298\,R^3$ points — close enough to the true $4R^3/\zeta(3) \approx 3.328\,R^3$. Here $R\ge 1$ is again arbitrary.

**Lemma 7 (multiples).** *Why we need this:* Counts how many vectors in $S$ are eliminated when we discard all multiples of an integer $j$.

For $j\ge 1$, the number of vectors $v\in S$ whose coordinates are all divisible by $j$ is at most $4(R/j)^3+5(R/j)^2$.

*Proof.* Put $r=\lfloor R/j\rfloor$. Any such vector has the form $jw$ with $|x(w)|,|y(w)|\le r$ and $1\le z(w)\le r$. The number of such $w$ is $(2r+1)^2r=4r^3+4r^2+r\le 4r^3+5r^2$, and $r\le R/j$. $\square$

Call $v\in S$ *primitive* if no prime divides all three of its coordinates, meaning its coordinates are coprime.

**Lemma 8 (primitive vectors).** *Why we need this:* Guarantees that distinct primitive vectors never collide under projection $\pi$, so counting primitive vectors lower-bounds $n = |P|$.

Distinct primitive vectors $u,v\in S$ satisfy $\pi(u)\ne\pi(v)$. Hence $n$ is at least the number of primitive vectors in $S$.

*Proof.* Let $v\in S$ be primitive, and let $t$ be any positive integer such that $t\,\pi(v) = (t\,x(v)/z(v),\,t\,y(v)/z(v))$ has integer coordinates. Then $z(v)$ divides $t\,x(v)$, $t\,y(v)$, and $t\,z(v)$, so it divides their greatest common divisor, which is $t \cdot \gcd(x(v), y(v), z(v)) = t$. Thus $z(v)$ is the smallest positive integer $t$ making $t\,\pi(v) \in \mathbb{Z}^2$. Therefore $\pi(v)$ uniquely determines $z(v)$ and hence $v = (z(v)\,\pi(v),\,z(v))$. $\square$

**Lemma 9 (many points).** *Why we need this:* Evaluates the union bound over $p \in \{2,3,5,7\}$ explicitly and bounds the tail over all larger odd integers by telescoping series.

$n\ge 3.298\,R^3-7R^2$.

*Proof.* If $v\in S$ is not primitive, some prime $p$ divides all three of its coordinates. Since $1 \le z(v) < R$, we have $p\le z(v)<R$, so $p$ is either $2,3,5,7$, or an odd integer $2i+1$ with $5\le i<R$. Since $|S|=4R^2(R-1) = 4R^3 - 4R^2$, Lemmas 7 and 8 give
$$n\ \ge\ 4R^3-4R^2-\sum_{j}\Bigl(\frac{4R^3}{j^3}+\frac{5R^2}{j^2}\Bigr),$$
where $j$ runs over $2,3,5,7$ and the odd numbers $2i+1$ with $5\le i<R$. (Not every such $j$ is prime, but dropping the primality restriction only increases the subtracted sum since every term is positive.)

To bound the tail over $i \ge 5$, use $(2i+1)^2\ge 4i(i+1)$:
$$\frac{1}{(2i+1)^2}\le\frac{1}{4i(i+1)}=\frac{1}{4}\Bigl(\frac{1}{i}-\frac{1}{i+1}\Bigr),$$
$$\frac{1}{(2i+1)^3}=\frac{2i+1}{(2i+1)^4}\le\frac{2i+1}{16\,i^2(i+1)^2}=\frac{1}{16}\Bigl(\frac{1}{i^2}-\frac{1}{(i+1)^2}\Bigr).$$
Both sums telescope cleanly, so over $i\ge 5$ they are at most $\frac{1}{4\cdot 5} = \frac{1}{20}$ and $\frac{1}{16\cdot 25} = \frac{1}{400}$, respectively. Substituting these bounds gives
$$n\ \ge\ 4\Bigl(1-\frac{1}{8}-\frac{1}{27}-\frac{1}{125}-\frac{1}{343}-\frac{1}{400}\Bigr)R^3
-\Bigl(4+\frac{5}{4}+\frac{5}{9}+\frac{5}{25}+\frac{5}{49}+\frac{5}{20}\Bigr)R^2.$$
The coefficient of $R^3$ (including the factor $4$) is $3.29819\ldots$, and the coefficient of $-R^2$ is $6.357\ldots$, yielding $n \ge 3.298\,R^3 - 7R^2$. $\square$

## Few points on a line

**Lemma 10 (points on a line).** *Why we need this:* Confirms that no single line holds too many points of $P$, giving $k = n - 2R^2$ very close to $n$.

Every line contains at most $2R^2$ points of $P$.

*Proof.* Every coordinate of a point in $P$ is a fraction $a/j$ with $-R\le a\le R-1$ and $1\le j\le R-1$, giving at most $2R(R-1)\le 2R^2$ possible coordinate values. Points on a non-vertical line have distinct first coordinates, and points on a vertical line have distinct second coordinates. $\square$

## Proof of the theorem

Let $R=30030M$ with $M\ge 1000$, so $R\ge 30\,030\,000$, and let $P=\pi(S)$ be the point set defined under Notation for this $R$. Lemma 10 gives the upper bound of $2R^2$ points per line.

For the point count, since $9R^2\le 0.0001R^3$ (as $R > 90\,000$), Lemma 9 gives
$$n\ \ge\ k=n-2R^2\ \ge\ 3.298R^3-9R^2\ \ge\ 3.2979R^3.$$
In particular $n\ge 3R^3$.

For the line count, since $30030\le R/1000$ and $16\le R/10^6$, Lemma 6 gives
$$L\ \le\ 1.8008\cdot 1.001^2R^6+10^{-6}R^6\ <\ 1.805R^6\ <\ 0.166\cdot 3.2979^2R^6\ \le\ 0.166\,kn.\qquad\square$$

## Remarks

1. *Scope.* The Theorem shows that the best constant $c$ in Beck's theorem is at most $0.166$. De Zeeuw (2018) proved that $c=1/9$ works.
2. *A better constant, not machine-checked.* Let $y\ge 2$, let $Q$ be the product of all primes $p\le y$, and use those primes in Lemma 5. For multiples $R$ of $Q$, the same calculation as in Lemma 6 gives
   $$L\le\frac{7}{2}\prod_{p\le y}(1-p^{-2})(1-p^{-3})\,R^4(R+Q)^2+16R^5.$$
   Because $S$, $P$, and hence $L$ never decrease when $R$ grows, any $R$ can be rounded up to the next multiple of $Q$. This gives $\limsup_{R\to\infty}L/R^6\le\frac{7}{2}\prod_{p\le y}(1-p^{-2})(1-p^{-3})$. Letting $y\to\infty$ yields $\limsup_{R\to\infty}L/R^6\le\frac{7}{2\zeta(2)\zeta(3)}$. By a standard count, $S$ contains $\frac{4}{\zeta(3)}R^3(1+o(1))$ primitive vectors, so $n\ge\frac{4}{\zeta(3)}R^3(1+o(1))$ and
   $$\limsup_{R\to\infty}\frac{L}{n^2}\ \le\ \frac{7\,\zeta(3)}{32\,\zeta(2)}<0.1599.$$

## What is new and what is borrowed

The question and the advice to look for a counterexample are Erdős's (*Research problems*, Period. Math. Hungar. 15 (1984), p. 103). Borwein and Moser repeated the question (Aequationes Math. 40 (1990), p. 124), printing $0\le k\le 2$, which appears to be a misprint for $0\le k\le n-2$; our theorem says nothing for $k\le 2$. The existence of some positive constant $c>0$ is due to Beck and to Szemerédi and Trotter (Combinatorica 3 (1983)), and the constant $1/9$ is due to de Zeeuw (arXiv:1802.08015).

The proof uses standard ingredients: rational points of bounded height, the subtractive Euclidean algorithm in a plane lattice, counting by residue classes, and a union bound over divisors. We do not claim the line count itself as new mathematics. The refutation appears to be new: two limited searches on 24-25 November 2026 found no earlier counterexample. Those searches looked for the result itself and predated the short proof given here; no separate search was done for this specific argument.

The novelty claim comes with a caveat involving a theorem of W. M. Schmidt. A rank-$2$ lattice has *shape* $\tau$ if it is similar to $\mathbb{Z}+\mathbb{Z}\tau$, where $\tau=\xi+i\eta$ lies in the standard modular fundamental domain $|\xi|\le\frac{1}{2}$, $|\tau|\ge 1$, $\eta>0$ (the choice between $\tau$ and $-\bar\tau$ does not matter here). Schmidt's theorem on sublattices of $\mathbb{Z}^m$ (Monatsh. Math. 125 (1998), as quoted in arXiv:0810.0234, Theorem 3.1) states that $\mathbb{Z}^3$ has about $\frac{2\pi}{3\zeta(3)}\mu(D)T^3$ primitive rank-$2$ sublattices with shape in $D$ and determinant at most $T$, where $\mu$ is the probability measure $\frac{3}{\pi}\,d\xi\,d\eta/\eta^2$ on the modular domain.

Replace our box by the half ball $x^2+y^2+z^2\le R^2$, $z\ge 1$. Up to $O(R^5)$ exceptions, the determined lines correspond to primitive sublattices whose second minimum (the length of the longer vector in a reduced basis) is at most $R$. For shape $\tau$ and determinant $d$, the second minimum is $|\tau|\sqrt{d/\eta}$, so the condition reads $d\le R^2\eta/|\tau|^2$. The change of variables $\tau\mapsto -1/\tau$ preserves $d\xi\,d\eta/\eta^2$ and sends $\eta/|\tau|^2$ to $\eta$. Thus $\int(\eta/|\tau|^2)^3\,d\mu$ equals $\frac{3}{\pi}$ times the integral of $\eta\,d\xi\,d\eta$ over $|\tau|\le 1$, $|\tau\pm 1|\ge 1$, $\eta>0$, which evaluates to $\frac{1}{4}$. This gives about $\frac{2\pi}{3\zeta(3)}\cdot\frac{3}{4\pi}R^6=R^6/(2\zeta(3))$ lines on about $2\pi R^3/(3\zeta(3))$ points, for a limiting ratio $L/n^2\to 9\zeta(3)/(8\pi^2)=0.1370$. We found no source making this deduction; it is sketched here only for comparison and is not used in the proof.

The short proof above (using boxes and the replacement step of Lemma 3) replaces an earlier proof by the same agents (not included in this repository) that used reduced bases and volumes to get the better constant $0.1605$. All of this work was produced by AI agents and has not been reviewed by a human expert.

## Lemma numbers and Lean names

The Lean file `Erdos211.lean` follows this writeup closely. All names below lie in the namespace `E211`, except `main`. The mathematics is the same, with a few minor differences in form:

* In Lean, $|S|$, $n$, and the line count are cardinalities of finite sets. The letter `L` there stands for a single line rather than the number of lines.
* Lemma 4.1 and Lemma 5 are multiplied by $2$ in Lean, and Lemma 4.2 is written without subtraction (`3 * M ^ 2 ≤ #(near M) + M`).
* $G$ is written out explicitly, and $G/Q^6<0.5145$ is checked as the integer inequality `prod_primes_le`.
* Lean allows $M=0$ in Lemmas 4 to 6 and $R=0$ in Lemmas 2, 3, 7, 8, and 10.

| Here | Lean |
|---|---|
| $S$, $\pi$, $P$ | `S`, `proj`, `P` |
| spanning, far, good | `Spans`, `Far`, `Good` |
| Lemma 1 | `combination` (replacing one vector: `Spans.replace`) |
| Lemma 2 | `convex` |
| Lemma 3 | `short_pair` (parts: `exists_short`, `Short.far`, `Short.no_combination`, `Short.good`) |
| Lemma 4 | `card_triangle`, `card_near`, `card_farBlocks` (the sets counted: `triangle`, `near`, `farBlocks`; $[-M,M)^2$: `square`) |
| Lemma 5 | `card_farPairs` (the pairs counted by $A$: `farPairs`; residues and quotients: `code`, `code_injective`, with `eq_of_residues` for the Chinese remainder theorem; independent pairs: `indepPairs`, `card_indepPairs`) |
| Lemma 6 | `few_lines` (the pairs counted by $B$: `levelPairs`, `card_levelPairs`; for $G$: `prod_primes_le`) |
| Lemma 7 | `card_multiples` (the vectors counted: `multiples`) |
| Lemma 8 | `proj_injOn` (primitive vectors: `primitive`; divisibility: `height_dvd`) |
| Lemma 9 | `many_points` (cover: `S_subset`; telescoping: `tail_term`, `tail_sum`) |
| Lemma 10 | `points_on_line` |
| Theorem | `counterexample` |
| Corollary | `main` |
