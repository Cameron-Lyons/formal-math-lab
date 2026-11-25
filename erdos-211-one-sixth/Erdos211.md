# Erdős Problem 211: the constant 1/6 in Beck's theorem fails

## The result

A line is *determined* by a finite set of points in the plane if it contains at least two of them. Beck, and
Szemerédi and Trotter, proved in 1983 that there is an absolute constant $c>0$ such that, for all $1\le k<n$, every set
of $n$ points with at most $n-k$ on any line determines at least $ckn$ lines. In 1984 Erdős wondered whether $c=1/6$
works, and advised to look for a counterexample first. We give one: there are arbitrarily large sets of $n$ points, with
only $O(n^{2/3})$ on any line, that determine at most $0.166\,n^2$ lines. So $c=1/6$ fails, even if the bound is only
asked for large $n$ and with a factor $1-\varepsilon$. Beck's theorem itself is not affected. The theorem contradicts the
bound $kn/6$ only for $k$ close to $n$: from about $0.996\,n$ on, and with the better constant of Remark 2 from about
$0.96\,n$ on. Nothing is claimed for smaller $k$.

**Theorem.** Let $M\ge 1000$ be an integer and $R=30030M$. There is a set $P$ of $n\ge 3R^3$ points in the plane
such that every line contains at most $2R^2$ points of $P$, and $P$ determines at most $0.166\,kn$ lines, where
$k=n-2R^2$.

**Corollary.** It is false that for every $\varepsilon>0$ there is an integer $N\ge1$ such that, for all $n\ge N$ and
$1\le k<n$, every set of $n$ points with at most $n-k$ on any line determines at least $(1-\varepsilon)kn/6$ lines.

*Proof of the corollary.* Suppose it is true, take the $N$ that belongs to $\varepsilon=1/1000$, and apply the
theorem with $M=\max(1000,N)$. Then $n\ge 3R^3\ge R\ge N$ and $n>2R^2>0$, so $1\le k<n$, and every line contains
at most $2R^2=n-k$ points. So $P$ determines at least $\frac{999}{6000}kn=0.1665\,kn>0.166\,kn$ lines, a
contradiction. $\square$

## The idea

Let $S$ be the set of the integer vectors $(x,y,z)$ in the box $[-R,R-1]^2\times[1,R-1]$, and let $P$ consist of the
points $(x/z,y/z)$ with $(x,y,z)\in S$. There are about $4R^3$ vectors in $S$. A proportion of about $1/\zeta(3)$ of
them is primitive, that is, has coprime coordinates. Different primitive vectors give different points, and dividing a
vector of $S$ by the greatest common divisor of its coordinates gives a primitive vector of $S$ with the same point. So
$P$ has about $4R^3/\zeta(3)$ points.

Two vectors $u,w\in S$ that give different points determine a line. For a given line choose $u,w$ so that the sum of
their third coordinates is as small as possible, and let $u$ have the larger one (the case of equality concerns only
$O(R^5)$ pairs). Then $u-w$ is not in the box, for otherwise it could take the place of $u$. So the first or the second
coordinates of $u$ and $w$ differ by at least $R$. Two random integers of $[-R,R-1]$ differ by less than $R$ with
probability about $3/4$, so this leaves a proportion of $1-(3/4)^2=7/16$ of all pairs. Also $u,w$ are linearly
independent modulo every prime $p$, for otherwise some $(au+bw)/p$ could take the place of one of them. For a random pair
this has probability $(1-p^{-2})(1-p^{-3})$, and the product over all $p$ is $1/(\zeta(2)\zeta(3))$. There are about
$\frac12(4R^3)^2$ pairs in which the third coordinate of $u$ is larger than that of $w$. So the number of lines is at most
about
$$\frac12\cdot\frac7{16}\cdot\frac{(4R^3)^2}{\zeta(2)\zeta(3)}\approx1.770\,R^6,\qquad\text{and}\qquad
\Bigl(\frac{4R^3}{\zeta(3)}\Bigr)^2\approx11.07\,R^6 .$$
The quotient is about $0.1599<1/6$. There is room to spare: in the proof below six primes are enough for the lines, and
a union bound is enough for the points.

## Notation

Throughout, $R\ge 1$ is an integer and
$$S=\{v=(x,y,z)\in\mathbb Z^3:\ -R\le x\le R-1,\ -R\le y\le R-1,\ 1\le z\le R-1\}.$$
We write $x(v),y(v),z(v)$ for the coordinates of $v$ and call $z(v)$ the *height* of $v$. For a vector $v$ of
positive height put $\pi(v)=(x(v)/z(v),\,y(v)/z(v))$. Let $P=\pi(S)$, $n=|P|$, and let $L$ be the number of lines
determined by $P$. The letter $p$ always denotes a prime.

A pair $(u,w)$ of vectors of $S$ is

* a *spanning pair* of a line $\ell$ if $\pi(u)\ne\pi(w)$ and both points lie on $\ell$;
* *far* if $|x(u)-x(w)|\ge R$ or $|y(u)-y(w)|\ge R$;
* *good at* $p$ if $u,w$ are linearly independent modulo $p$, as vectors of $\mathbb F_p^3$.

## Few lines

**Lemma 1 (combinations).** Let $u,w,v$ be integer vectors of positive height with $\pi(u)\ne\pi(w)$, and let
$mv=au+bw$ with integers $m\ge1$, $a$, $b$, $b\neq0$. Then $\pi(v)\ne\pi(u)$, and $\pi(v)$ lies on the line through
$\pi(u)$ and $\pi(w)$.

*Proof.* Put $t=\dfrac{b\,z(w)}{m\,z(v)}\ne0$. Since $m\,z(v)=a\,z(u)+b\,z(w)$, we have
$\dfrac{a\,z(u)}{m\,z(v)}=1-t$. Hence
$$\frac{x(v)}{z(v)}=\frac{a\,x(u)+b\,x(w)}{m\,z(v)}=(1-t)\frac{x(u)}{z(u)}+t\,\frac{x(w)}{z(w)},$$
and the same holds for $y$. So $\pi(v)=(1-t)\pi(u)+t\,\pi(w)$ with $t\ne0$. $\square$

So, if $(u,w)$ is a spanning pair of $\ell$ and $v\in S$, $mv=au+bw$ with $m\ge1$, then $(u,v)$ is a spanning pair of
$\ell$ when $b\ne0$ ("$v$ can replace $w$"), and $(v,w)$ is one when $a\neq0$ ("$v$ can replace $u$").

**Lemma 2 (convexity).** Let $u,w\in S$ and $mv=au+bw$ with $v\in\mathbb Z^3$ and integers $a,b\ge0$, $1\le a+b\le m$.
Then $v\in S$.

*Proof.* Since $R-1\ge0$, we have $m\,x(v)\le(a+b)(R-1)\le m(R-1)$ and $m\,x(v)\ge-(a+b)R\ge-mR$, and the same for $y$.
Similarly $m\,z(v)\le m(R-1)$. Finally $m\,z(v)=a\,z(u)+b\,z(w)>0$, so the integer $z(v)$ is at least $1$. $\square$

**Lemma 3 (short pairs).** Every determined line has a spanning pair $(u,w)$ with $z(u)=z(w)$, or with $z(u)>z(w)$ that
is far and good at every prime.

*Proof.* Among the spanning pairs of the line choose one with $z(u)+z(w)$ minimal. Spanning pairs may be swapped, so let
$z(u)\ge z(w)$, and suppose $z(u)>z(w)$.

*Far.* If $(u,w)$ is not far, then $v=u-w$ has $|x(v)|,|y(v)|\le R-1$ and $1\le z(v)\le R-1$, so $v\in S$. Since
$v=u-w$, Lemma 1 shows that $v$ can replace $u$. But $z(v)+z(w)=z(u)<z(u)+z(w)$, a contradiction.

*Good.* Suppose that $u,w$ are dependent modulo a prime $p$. Then there are integers $a,b\in[0,p-1]$, not both $0$, such
that $au+bw=pv$ with $v\in\mathbb Z^3$. If $a+b>p$, then $a,b\ge1$, and we replace $(a,b,v)$ by $(p-a,\,p-b,\,u+w-v)$.
The new $a,b$ are again in $[1,p-1]$, and their sum is less than $p$. So we may assume $1\le a+b\le p$, and $v\in S$ by
Lemma 2.

* If $a=0$, then $b\geq 1$ and $v$ can replace $w$. But $z(v)=\frac bp z(w)<z(w)$, a contradiction.
* If $a>0$, then $v$ can replace $u$. But $p\,z(v)=a\,z(u)+b\,z(w)<p\,z(u)$: for $b=0$ because $a<p$, and for $b>0$
  because $z(w)<z(u)$ and $a+b\le p$. Again a contradiction. $\square$

**Lemma 4 (far blocks).** Let $M\ge1$ be an integer, and write $[-M,M)$ for the set of the integers $i$ with $-M\le i<M$.

1. There are $M(M+1)/2$ pairs of integers $(i,j)$ with $0\le i\le j<M$.
2. Call $(i,j)\in[-M,M)^2$ *near* if $|i-j|<M$. There are at least $3M^2-M$ near pairs.
3. There are at most $7M^3(M+1)$ *far blocks*, that is, pairs $(q,q')$ of elements of $[-M,M)^2$, at least one of which is
   not near.

*Proof.* (1) is clear. (2) Let $(i,j)\in[-M,M)^2$ be not near. If $j\ge i+M$, then $0\le i+M\le j<M$, so $(i+M,j)$ is one
of the pairs in (1), and it determines $(i,j)$. Otherwise $i\ge j+M$, and in the same way $(j+M,i)$ is one of the pairs
in (1). So there are at most $M(M+1)$ pairs that are not near, and at least $4M^2-M(M+1)=3M^2-M$ near ones. (3) There are
$(4M^2)^2$ pairs $(q,q')$, and by (2) both elements are near in at least $(3M^2-M)^2$ of them. So the number of far blocks
is at most $16M^4-(3M^2-M)^2=7M^4+6M^3-M^2\le 7M^3(M+1)$. $\square$

From now on let $M\ge1$ be an integer, $Q=30030=2\cdot3\cdot5\cdot7\cdot11\cdot13$, $R=QM$, and
$$G=\prod_{p\in\{2,3,5,7,11,13\}}(p^3-1)(p^3-p).$$

**Lemma 5 (far pairs).** Let $A$ be the number of pairs $(u,w)$ of vectors of $S$ with $z(u)>z(w)$ that are far and good
at the six primes $2,3,5,7,11,13$. Then
$$A\le 7M^3(M+1)\cdot\frac{M(M+1)}2\cdot G.$$

*Proof.* To a pair $(u,w)$ we assign its residues modulo the six primes, and the quotients $\lfloor\cdot/Q\rfloor$ of its six
coordinates. By the Chinese remainder theorem the residues determine $(u,w)$ modulo $Q$, so together with the quotients they
determine $(u,w)$. We count the possible values.

* *Residues modulo $p$.* The pair is independent in $\mathbb F_p^3$. There are $(p^3-1)(p^3-p)$ independent pairs: the
  first vector is not zero, and the second is not one of the $p$ multiples of the first. In all there are $G$ possibilities.
* *Quotients of $z(w),z(u)$.* Let them be $i,j$. Since $0<z(w)<z(u)<QM$, we have $0\le i\le j<M$. By Lemma 4(1) there are
  $M(M+1)/2$ possibilities.
* *Quotients of the other coordinates.* Those of $x(u),x(w)$ form a pair $(i,i')\in[-M,M)^2$, and those of $y(u),y(w)$ another
  one. If $|i-i'|\le M-1$, then $|x(u)-x(w)|\le Q(M-1)+(Q-1)=R-1$, and the same holds for $y$. Since $(u,w)$ is far, at least
  one of the two pairs is not near, so they form a far block. By Lemma 4(3) there are at most $7M^3(M+1)$ possibilities.
  $\square$

**Lemma 6 (few lines).** $L\le 1.8008\,R^4(R+30030)^2+16R^5$.

*Proof.* A spanning pair determines its line, so Lemma 3 gives $L\le A+B$, where $B$ is the number of pairs $(u,w)$ of
vectors of $S$ with $z(u)=z(w)$. Clearly $B\le|S|\cdot(2R)^2\le4R^3\cdot4R^2=16R^5$. Next,
$$\frac G{Q^6}=\prod_{p\in\{2,3,5,7,11,13\}}\Bigl(1-\frac1{p^2}\Bigr)\Bigl(1-\frac1{p^3}\Bigr)<
0.65625\cdot0.855968\cdot0.95232\cdot0.976736\cdot0.990991\cdot0.993631<0.5145,$$
and $Q^6M^4(M+1)^2=R^4(R+Q)^2$. By Lemma 5, $A\le\frac72\cdot0.5145\,R^4(R+Q)^2\le1.8008\,R^4(R+Q)^2$. $\square$

## Many points

Here $R\ge1$ is arbitrary again.

**Lemma 7 (multiples).** For $j\ge1$, the number of $v\in S$ whose coordinates are all divisible by $j$ is at most
$4(R/j)^3+5(R/j)^2$.

*Proof.* Put $r=\lfloor R/j\rfloor$. Such a vector is $jw$ with $|x(w)|,|y(w)|\le r$ and $1\le z(w)\le r$. The number of
these $w$ is $(2r+1)^2r=4r^3+4r^2+r\le4r^3+5r^2$, and $r\le R/j$. $\square$

Call $v\in S$ *primitive* if no prime divides all three coordinates, that is, if they are coprime.

**Lemma 8 (primitive vectors).** Distinct primitive vectors $u,v\in S$ have $\pi(u)\ne\pi(v)$. So $n$ is at least the number
of primitive vectors in $S$.

*Proof.* Let $v\in S$ be primitive, and let $t$ be a positive integer such that $t\,\pi(v)$ has integer coordinates. Then
$z(v)$ divides $t\,x(v)$, $t\,y(v)$ and $t\,z(v)$, hence their greatest common divisor, which is $t$. So $z(v)$ is the least
such $t$. Hence $\pi(v)$ determines $z(v)$, and $v$. $\square$

**Lemma 9 (many points).** $n\ge3.298\,R^3-7R^2$.

*Proof.* Let $v\in S$ be not primitive, and let the prime $p$ divide its coordinates. Then $p\le z(v)<R$, and $p$ is
$2$, $3$, $5$, $7$, or an odd number $2i+1$ with $5\le i<R$. Since $|S|=4R^2(R-1)$, Lemmas 7 and 8 give
$$n\ \ge\ 4R^3-4R^2-\sum_{j}\Bigl(\frac{4R^3}{j^3}+\frac{5R^2}{j^2}\Bigr),$$
where $j$ runs over $2,3,5,7$ and the numbers $2i+1$ with $5\le i<R$. (Not every such $j$ occurs as a $p$, but all terms
are positive.) Since $(2i+1)^2\ge4i(i+1)$,
$$\frac1{(2i+1)^2}\le\frac1{4i(i+1)}=\frac14\Bigl(\frac1i-\frac1{i+1}\Bigr),\qquad
\frac1{(2i+1)^3}=\frac{2i+1}{(2i+1)^4}\le\frac{2i+1}{16\,i^2(i+1)^2}=\frac1{16}\Bigl(\frac1{i^2}-\frac1{(i+1)^2}\Bigr).$$
These sums telescope, so over $i\ge5$ they are at most $\frac1{20}$ and $\frac1{400}$. Hence
$$n\ \ge\ 4\Bigl(1-\frac18-\frac1{27}-\frac1{125}-\frac1{343}-\frac1{400}\Bigr)R^3
-\Bigl(4+\frac54+\frac59+\frac5{25}+\frac5{49}+\frac5{20}\Bigr)R^2.$$
The coefficient of $R^3$ (with the factor $4$) is $3.29819\ldots$, and that of $-R^2$ is $6.357\ldots$. $\square$

## Few points on a line

**Lemma 10 (points on a line).** Every line contains at most $2R^2$ points of $P$.

*Proof.* Each coordinate of a point of $P$ is a fraction $a/j$ with $-R\le a\le R-1$ and $1\le j\le R-1$. There are at most
$2R(R-1)\le2R^2$ such numbers. If the line is not vertical, its points have distinct first coordinates. If it is vertical,
its points have distinct second coordinates. $\square$

## Proof of the theorem

Let $R=30030M$ with $M\ge1000$, so that $R\ge30\,030\,000$, and let $P=\pi(S)$ be the set defined under Notation for this
$R$. The bound for the points on a line is Lemma 10. By Lemma 9, and because $9R^2\le0.0001R^3$,
$$n\ \ge\ k=n-2R^2\ \ge\ 3.298R^3-9R^2\ \ge\ 3.2979R^3 .$$
In particular $n\ge3R^3$. Since $30030\le R/1000$ and $16\le R/10^6$, Lemma 6 gives
$$L\ \le\ 1.8008\cdot1.001^2R^6+10^{-6}R^6\ <\ 1.805R^6\ <\ 0.166\cdot3.2979^2R^6\ \le\ 0.166\,kn.\qquad\square$$

## Remarks

1. *Scope.* The theorem shows that the best constant $c$ in Beck's theorem is at most $0.166$. De Zeeuw (2018) proved that
   $c=1/9$ is admissible.
2. *A better constant, not machine-checked.* Let $y\ge2$, let $Q$ be the product of all primes $p\le y$, and use these primes
   in Lemma 5. For the multiples $R$ of $Q$ this gives, as in Lemma 6,
   $L\le\frac72\prod_{p\le y}(1-p^{-2})(1-p^{-3})\,R^4(R+Q)^2+16R^5$. Since $S$, $P$ and hence $L$ do not decrease when $R$
   grows, an arbitrary $R$ may be rounded up to the next multiple of $Q$. So
   $\limsup_{R\to\infty}L/R^6\le\frac72\prod_{p\le y}(1-p^{-2})(1-p^{-3})$. With $y\to\infty$ we get
   $\limsup_{R\to\infty}L/R^6\le\frac72\cdot\frac1{\zeta(2)\zeta(3)}$. Since $S$ has $\frac{4}{\zeta(3)}R^3(1+o(1))$
   primitive vectors (a standard count), $n\ge\frac4{\zeta(3)}R^3(1+o(1))$. So
   $$\limsup_{R\to\infty}\frac L{n^2}\ \le\ \frac{7\,\zeta(3)}{32\,\zeta(2)}<0.1599.$$

## What is new and what is borrowed

The question, and the advice to look for a counterexample, are Erdős's (*Research problems*, Period. Math. Hungar. 15 (1984),
p. 103). The question was repeated by Borwein and Moser (Aequationes Math. 40 (1990), p. 124). They print the conjecture for
$0\le k\le2$, apparently a misprint for $0\le k\le n-2$; for $k\le2$ the theorem above says nothing. The bound with some
constant $c>0$ is due to Beck and to Szemerédi and Trotter (Combinatorica 3 (1983)); the constant $1/9$ is due to de Zeeuw
(arXiv:1802.08015). The ingredients of the proof are standard: rational points of bounded height, the subtractive Euclidean
algorithm in a plane lattice, counting by residue classes, and a union bound over divisors. The line count itself is not
claimed as new mathematics. The refutation is new as far as known: two limited searches on 24–25 November 2026 found no
earlier counterexample. They concerned the result, and predate the short proof given here; no separate search for its argument
is on record.

The novelty claim is limited by the following. A lattice of rank $2$ has *shape* $\tau$ if it is similar to
$\mathbb Z+\mathbb Z\tau$, where $\tau=\xi+i\eta$ lies in the usual modular domain $|\xi|\le\frac12$, $|\tau|\ge1$, $\eta>0$.
(The choice between $\tau$ and $-\bar\tau$ plays no role here.) A theorem of W. M. Schmidt on sublattices of $\mathbb Z^m$
(Monatsh. Math. 125 (1998), as quoted in arXiv:0810.0234, Theorem 3.1) says that $\mathbb Z^3$ has about
$\frac{2\pi}{3\zeta(3)}\mu(D)T^3$ primitive sublattices of rank $2$ with shape in $D$ and determinant at most $T$, where
$\mu$ is the probability measure $\frac3\pi\,d\xi\,d\eta/\eta^2$ on the modular domain. Replace the box by the half ball
$x^2+y^2+z^2\le R^2$, $z\ge1$. Up to $O(R^5)$ exceptions the lines correspond to the primitive sublattices whose second
minimum (the length of the longer vector of a reduced basis) is at most $R$. For shape $\tau$ and determinant $d$ the second
minimum is $|\tau|\sqrt{d/\eta}$, so the condition is $d\le R^2\eta/|\tau|^2$. The substitution $\tau\mapsto-1/\tau$ preserves
$d\xi\,d\eta/\eta^2$ and turns $\eta/|\tau|^2$ into $\eta$. So $\int(\eta/|\tau|^2)^3\,d\mu$ is $\frac3\pi$ times the integral of
$\eta\,d\xi\,d\eta$ over the region $|\tau|\le1$, $|\tau\pm1|\ge1$, $\eta>0$, which is $\frac14$. Hence there are about
$\frac{2\pi}{3\zeta(3)}\cdot\frac3{4\pi}R^6=R^6/(2\zeta(3))$ lines, on about $2\pi R^3/(3\zeta(3))$ points, and the ratio of
lines to $n^2$ tends to $9\zeta(3)/(8\pi^2)=0.1370$. No one was found who made this deduction. It is sketched only for
comparison, and is not used here.

The short proof above, with boxes and the replacement argument of Lemma 3, replaces an earlier one by the same agents
(not included in this repository) that used reduced bases and volumes and gave the better constant $0.1605$. All of this was
produced by AI agents, and has not been reviewed by a human expert.

## Lemma numbers and Lean names

The file `Erdos211.lean` follows this text. The names below are in the namespace `E211`, except `main`. The content is the
same, with these differences in form.

* In Lean, $|S|$, $n$ and the number of lines are cardinalities of finite sets. The letter `L` there stands for a line, not
  for the number of lines.
* Lemma 4.1 and Lemma 5 are multiplied by $2$ in Lean, and Lemma 4.2 is written without subtraction
  (`3 * M ^ 2 ≤ #(near M) + M`).
* $G$ is written out, and $G/Q^6<0.5145$ is the integer inequality `prod_primes_le`.
* Lean allows $M=0$ in Lemmas 4–6 and $R=0$ in Lemmas 2, 3, 7, 8 and 10.

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
