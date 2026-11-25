# Erdős Problem 1066 in higher dimensions: no uniform lower bound $c\,n/d$

## The theorem

Take $n$ points in $d$-dimensional space, no two closer than $1$. How many of them can we always keep so that all
remaining distances are strictly greater than $1$? Let $g_d(n)$ be the largest $k$ such that every set of $n$ points of
$\mathbb R^d$ with pairwise distances at least $1$ contains $k$ points with pairwise distances greater than $1$.
Problem 1066 itself asks for the size of $g_2(n)$; nothing is said about this planar case here.

R. Pollack (J. Combin. Theory Ser. A 40 (1985) 450) reports a letter in which "Erdős asks for a proof or disproof of
$f(n,k)>cn/k$"; his $f(n,k)$ is $g_k(n)$, where $k$ is the dimension and $n$ the number of points. We read $c>0$ as a
constant that depends neither on the dimension nor on $n$. This is also the reading of Formal Conjectures
(`Erdos1066.erdos_1066.variants.higher_dim`, the statement whose negation is proved in Lean). With this reading the
answer is no.

**Theorem.** Let $A=2^m$ with an integer $m\ge 0$, and put $d=6A^2$, $n=4A^4$. Then $g_d(n)\le 2A+2$.

**Corollary.** There is no $c>0$ such that $g_d(n)\ge c\,n/d$ for all $d\ge 1$ and all $n\ge 0$.

*Proof of the Corollary.* If there were, the Theorem would give
$\tfrac{2}{3}cA^2=c\cdot\frac{4A^4}{6A^2}\le 2A+2\le 4A$, that is, $cA\le 6$ for every $A=2^m$. This is false for
large $m$. $\blacksquare$

The Corollary refutes even the non-strict form of Erdős's inequality. The answer is the same if only large $n$ are
considered (see the Remark *Large $n$*).

The vectors below are not new. The Corollary already follows from Lemma 1 and a theorem of D. de Caen (2000) on
equiangular lines, quoted in the section *What is borrowed*; a reader who accepts that theorem can stop after Lemma 1.
Lemmas 2 to 5 give a self-contained construction.

**Idea.** Suppose we have $n$ vectors of squared length $L$ whose pairwise inner products are all $+A$ or $-A$. Then
there are at most two distances, and inner product $+A$ belongs to the smaller one. If $k$ of the vectors are pairwise at
the larger distance, their pairwise inner products are all $-A$, and $0\le\lVert\sum w\rVert^2=kL-k(k-1)A$ gives
$k\le1+L/A$. We shall have $L=2A^2+A$, so $k\le 2A+2$. It remains to find many such vectors in a space of low dimension.
They come from the functions $x\mapsto\chi(cx,bx)$ on a field $F$ with $2A^2$ elements, where $\chi$ is a character of
$F\times F$ with a slightly twisted addition. The inner product of two of these functions has real part $\pm A$ if the
$c$'s differ, and it is $0$ if the $c$'s agree and the $b$'s differ. An additional entry $\sqrt A$, in a place that
depends on $c$ only, turns this $0$ into $+A$.

## Lemma 1 (vectors with inner products $\pm A$)

Let $A\ge 1$ be an integer, and let $w_1,\dots,w_n$ be vectors in a real inner product space of dimension $d$ with
$\lVert w_j\rVert^2=2A^2+A$ and $\langle w_j,w_l\rangle\in\{A,-A\}$ for $j\ne l$.

(a) If $k$ of these vectors have all pairwise inner products equal to $-A$, then $k\le 2A+2$.

(b) $g_d(n)\le 2A+2$.

*Proof.* (a) We may assume $k\ge1$. If $w$ runs over these $k$ vectors, then
$$0\le\Big\lVert\sum w\Big\rVert^2=k(2A^2+A)-k(k-1)A=kA\,(2A+2-k).$$
Divide by $kA>0$.

(b) The space may be taken to be $\mathbb R^d$. Let $p_j=w_j/(2A)$. For $j\neq l$,
$$\lVert p_j-p_l\rVert^2=\frac{2(2A^2+A)-2\langle w_j,w_l\rangle}{4A^2}=1+\frac{A-\langle w_j,w_l\rangle}{2A^2}.$$
This is $1$ if $\langle w_j,w_l\rangle=A$, and $1+1/A>1$ if $\langle w_j,w_l\rangle=-A$. So the $n$ points $p_j$ are
distinct, their pairwise distances are at least $1$, and a distance is greater than $1$ only if the inner product of the
two vectors is $-A$. By (a), at most $2A+2$ of the points have pairwise distances greater than $1$. $\blacksquare$

## Lemma 2 (two squares)

Let $u,v$ be integers with $u^2+v^2=2^{2m+1}$, $m\ge 0$. Then $u=\pm2^m$.

*Proof.* Induction on $m$. If $m=0$, then $u^2+v^2=2$, so $u=\pm1$. Let $m\ge1$. A square is $0$ or $1$ modulo $4$,
according as its root is even or odd. Since $4\mid u^2+v^2$, both $u$ and $v$ are even. Now
$(u/2)^2+(v/2)^2=2^{2(m-1)+1}$, so $u/2=\pm2^{m-1}$ by induction. $\blacksquare$

## Lemma 3 (the group $W$ and its characters)

From now on $A=2^m$, and $F$ is the field with $q=2^{2m+1}=2A^2$ elements. Since $F$ has characteristic $2$, we have
$t+t=0$, that is, $-t=t$, for all $t\in F$. Let $W=F\times F$ with the addition
$$(a,b)+(a',b')=(a+a',\;b+b'+aa').$$
This is an abelian group. It is commutative; both ways of adding three elements give
$(a+a'+a'',\,b+b'+b''+aa'+aa''+a'a'')$; the zero is $(0,0)$; and $-(a,b)=(a,\,b+a^2)$. Two special cases will be used:
$$(a,b)+(0,t)=(a,b+t),\qquad -(0,t)=(0,t).\tag{1}$$
A *character* of $W$ is a homomorphism $\chi$ from $W$ to the multiplicative group of nonzero complex numbers; so
$\chi(-p)=1/\chi(p)$. We write $\chi(a,b)$ for $\chi((a,b))$.

(a) There is a character $\chi$ of $W$ with $\chi(0,1)\ne1$. We fix one.

(b) If $t\in F$ is nonzero, then $\sum_{x\in F}\chi(0,tx)=0$.

(c) For every $p\in W$ we have $\chi(p)=u+iv$ with integers $u,v$ and the imaginary unit $i$, and
$\chi(-p)=\overline{\chi(p)}$.

*Proof.* (a) For every nonzero element $p$ of a finite abelian group there is a character with value $\ne1$ at $p$
(textbook fact).

(b) By (1), $(0,t(x+1/t))=(0,tx)+(0,1)$. So replacing $x$ by $x+1/t$ multiplies every term by $\chi(0,1)$. The sum $T$
therefore satisfies $T=\chi(0,1)\,T$, and $T=0$.

(c) We have $2(a,b)=(0,a^2)$ and hence $4(a,b)=(0,0)$. So $\chi(p)^4=\chi(0)=1$, and $\chi(p)\in\{1,-1,i,-i\}$. Since
$|\chi(p)|=1$, we get $\chi(-p)=1/\chi(p)=\overline{\chi(p)}$. $\blacksquare$

## Lemma 4 (the character sums)

Let $c,b,c',b'\in F$ (so $c$ is no longer the constant of the Corollary) and put
$$\delta(x)=(cx,bx)-(c'x,b'x)\in W\quad(x\in F),\qquad S=\sum_{x\in F}\chi(\delta(x)).$$

(a) If $c=c'$ and $b\ne b'$, then $S=0$.

(b) If $c\ne c'$, then $|S|^2=q$.

(c) If $c\ne c'$, then $\operatorname{Re}S=\pm A$.

*Proof.* (a) By (1), $(cx,bx)=(cx,0)+(0,bx)$ and $(cx,b'x)=(cx,0)+(0,b'x)$. So
$\delta(x)=(0,bx)-(0,b'x)=(0,(b+b')x)$. Since $b\ne b'$, we have $b+b'\ne0$. Use Lemma 3(b).

(b) Put $e=c+c'\neq0$. By the definition of the addition and (1),
$(cx+cy,\,bx+by)=(cx,bx)+(cy,by)+(0,c^2yx)$. Subtract from this the same equation for $c',b'$. By (1) and
$c^2+c'^2=e^2$,
$$\delta(x+y)=\delta(x)+\delta(y)+(0,e^2yx).\tag{2}$$
In the double sum for $|S|^2=S\,\overline S$ write the first summation index as $x+y$ and the second as $x$, and use
Lemma 3(c) and (2):
$$|S|^2=\sum_{x,y}\chi(\delta(x+y))\,\overline{\chi(\delta(x))}=\sum_{x,y}\chi(\delta(x+y)-\delta(x))
=\sum_{y}\chi(\delta(y))\sum_{x}\chi(0,e^2y\,x).$$
For $y\ne0$ the inner sum is $0$ by Lemma 3(b). For $y=0$ it is $q$, because $\chi(0,0)=1$, and $\chi(\delta(0))=1$,
because $\delta(0)=0$. So $|S|^2=q$.

(c) By Lemma 3(c), $S=U+iV$ with integers $U,V$, and (b) says $U^2+V^2=2^{2m+1}$. By Lemma 2, $U=\pm2^m=\pm A$.
$\blacksquare$

## Lemma 5 (the vectors)

We work in $\mathbb C^q\oplus\mathbb R^q$, with coordinates indexed by $F$. This is a real inner product space of
dimension $3q$ with
$$\langle(z,s),(z',s')\rangle=\operatorname{Re}\sum_{x\in F}z_x\overline{z'_x}+\sum_{x\in F}s_xs'_x.$$
For $c,b\in F$ let $w_{c,b}$ be the vector whose first part is $\big(\chi(cx,bx)\big)_{x\in F}$ and whose second part
has the entry $\sqrt A$ in position $c$ and $0$ elsewhere.

(a) $\lVert w_{c,b}\rVert^2=2A^2+A$.

(b) If $(c,b)\ne(c',b')$, then $\langle w_{c,b},w_{c',b'}\rangle=\pm A$.

*Proof.* By Lemma 3(c), $\chi(cx,bx)\,\overline{\chi(c'x,b'x)}=\chi(\delta(x))$. Hence, with $S$ as in Lemma 4,
$$\langle w_{c,b},w_{c',b'}\rangle=\operatorname{Re}S+\begin{cases}A&\text{if }c=c',\\0&\text{if }c\ne c'.\end{cases}$$

(a) If $(c,b)=(c',b')$, then $\delta(x)=0$ for all $x$. So $S=q=2A^2$, and the formula gives $2A^2+A$.

(b) If $c=c'$ and $b\ne b'$, then $S=0$ by Lemma 4(a), and the formula gives $A$. If $c\ne c'$, it gives
$\operatorname{Re}S=\pm A$ by Lemma 4(c). $\blacksquare$

## Proof of the Theorem

Lemma 5 gives $q^2=4A^4$ vectors in dimension $3q=6A^2$ that satisfy the hypotheses of Lemma 1. Lemma 1(b) gives
$g_{6A^2}(4A^4)\le 2A+2$. $\blacksquare$

## Remarks

* *All dimensions.* Since $\mathbb R^d\subset\mathbb R^{d'}$ for $d\le d'$, $g_d(n)$ does not increase with $d$. For
  $d\ge6$ choose the power of two $A$ with $6A^2\le d<24A^2$, and $n=4A^4$. Then
  $g_d(n)\le 2A+2\le4A=n/A^3\le 24^{3/2}\,n/d^{3/2}$. For $d<6$ this bound holds with $n=1$. So for every $d\ge1$ there
  is $n\ge1$ with $g_d(n)\le118\,n/d^{3/2}$.
* *Large $n$.* Take $N$ copies of a set of $n$ points, placed far apart. If at most $k$ points can be kept from the
  set, then at most $Nk$ can be kept from all copies together. So $g_d(Nn)\le N\,g_d(n)$. Hence the bound
  $118\,n/d^{3/2}$ holds, for every $d\ge1$, for arbitrarily large $n$. The Theorem gives
  $g_{6A^2}(4A^4N)\le(2A+2)N$ for all $N\ge1$, so, as in the proof of the Corollary, there is no $c>0$ such that, for
  every $d\ge1$, $g_d(n)\ge c\,n/d$ holds for all sufficiently large $n$.
* *Small dimension.* Disjoint regular simplices of side $1$ with at most $d+1$ vertices each, placed far apart, give
  $g_d(n)\le\lceil n/(d+1)\rceil$, because at most one vertex of each can be kept. The Theorem is better than this from
  $A=4$ on ($10$ against $11$ for $n=1024$, $d=96$), because $4A^4>(2A+2)(6A^2+1)$ for $A\ge4$. At $A=4$, however, two
  configurations cited below have more points in a smaller dimension, again with at most $10$ kept: $1460$ points in
  $\mathbb R^{73}$ (Ismailescu, Lee and Lee) and $2048$ points in $\mathbb R^{95}$ (de Caen). The ratio $n/(2d)$, which
  Ismailescu, Lee and Lee reach for other $n$ and $d$, is $A^2/3$ at the parameters of the Theorem; this exceeds $2A+2$
  from $A=8$ on.
* *Limits of the result.* The exponent $3/2$ is not claimed to be optimal. If $c$ may depend on $d$, then
  $g_d(n)\ge c\,n/d$ is trivially true: a point has at most $\kappa_d$ others at distance exactly $1$ ($\kappa_d$ is
  the kissing number), so choosing points greedily keeps at least $n/(\kappa_d+1)$.

The proof and the remarks on it end here. The rest is about sources, priority and the Lean file.

## What is borrowed

*The vectors.* D. de Caen (*Large equiangular sets of lines in Euclidean space*, Electron. J. Combin. 7 (2000) R55)
found $\frac29(d+1)^2$ unit vectors in $\mathbb R^d$, $d=3\cdot2^{2t-1}-1$, with all inner products of distinct vectors
$\pm1/(2^t+1)$. Put $A=2^{t-1}$ and multiply them by $\sqrt{A(2A+1)}$. This gives $8A^4$ vectors in dimension $6A^2-1$
with $\lVert w\rVert^2=2A^2+A$ and pairwise inner products $\pm A$, so Lemma 1 yields $g_{6A^2-1}(8A^4)\le2A+2$: twice
as many points as in the Theorem, in one dimension fewer. So the Corollary is an immediate consequence of a published
theorem.

*The construction.* Lemma 4 is about mutually unbiased bases. For fixed $c$, the $q$ vectors
$\big(\chi(cx,bx)/\sqrt q\big)_{x\in F}$, $b\in F$, form an orthonormal basis of $\mathbb C^q$ (Lemma 4(a)), and vectors
from two of these bases have inner products of absolute value $1/\sqrt q$ (Lemma 4(b)). Greaves, Koolen, Munemasa and
Szöllősi (*Equiangular lines in Euclidean spaces*, arXiv:1403.2155, Theorem 2.5) obtain de Caen's parameters from
mutually unbiased bases of $\mathbb R^N$, $N=4A^2$ (orthonormal bases such that vectors from different bases have inner
product $\pm1/\sqrt N$), with additional coordinates of the kind used in Lemma 5. Such bases come from Kerdock sets
(Kerdock 1972; Cameron and Seidel 1973; Calderbank, Cameron, Kantor and Seidel 1997). The group $W$ is the additive
group of the Witt vectors of length two over $F$, and its use is the $\mathbb Z/4$ description of Kerdock codes by
Hammons, Kumar, Calderbank, Sloane and Solé (1994).

## What appears to be new

Only a link, and only part of it. Lemma 1 is in effect already used, for one special system of lines, by Ismailescu, Lee
and Lee (arXiv:2611.23767, 18 November 2026): their points are the vectors $\pm v$ for $r^3+1$ unit vectors in dimension
$r^2-r+1$ with inner products $\pm1/r$ (Taylor's regular two-graphs), and they bound the number of points that can be kept
by the same norm-of-the-sum argument. They do not mention equiangular lines or de Caen, and that system gives only
$n/(2d)$. What we did not find anywhere is that large equiangular systems can be used in general, which turns $n/d$ into
order $n/d^{3/2}$, or any answer to Erdős's question. A GitHub repository of May 2026, Dr-How/chromatic-sphere-packing
(a generated draft), conjectures the opposite: that the chromatic number of contact graphs of unit balls is $O(d)$, which it
calls equivalent to keeping at least $n/(Cd)$ points. The Theorem refutes the second statement, hence also the first.

All families of upper bounds for $g_d(n)$ with growing $d$ that we found in print are of order $n/d$. Examples:
* $\lceil n/(d+1)\rceil$ from simplices;
* $6n/(6d+7)$, for suitable $n$ (Pach; Graham and Chung, in Pollack's note);
* $n/(r^3+1)$ for $n=(r+1)(r^3+1)$, $d=r^3-r^2+r$, with $r$ a power of a prime (H. Chen, arXiv:1502.02070);
* $n/(2d)$ for $n=2(r^3+1)$, $d=r^2-r+1$, with $r$ a power of an odd prime (Ismailescu, Lee and Lee, arXiv:2611.23767).

The last two are stated there as lower bounds for chromatic numbers, but the proofs bound the quotient $n/k$ from below,
where $k$ is the largest number of points that can be kept. G. Kalai's survey arXiv:1505.04952 contains both de Caen's
theorem (Theorem 2.6) and a question on minimum-distance graphs (Problem 5.1), without linking them, so the observation
may be known to experts.

The searches (three, 24-25 November 2026, the last one for this vocabulary) were limited. The main unread source is Bezdek, Naszódi and Visy (*On the mth Petty
numbers of normed spaces*, 2003). The problem's page and forum thread (four posts) on the Erdős problems site were not
read either. Another site's entry for the problem, https://www.erdosproblemaday.com/problem/1066, dated 29 July 2026,
lists it as open and says that the official page then showed "a claimed proof or a listed worker". It gives no
details, so we do not know what this refers to.

Generated by an AI agent and machine-checked; not reviewed by a human expert. The Theorem and the Corollary, with the
Lemmas, are machine-checked. The Remarks are not (an earlier Lean proof has the bound of *All dimensions*, with
$2^{21}$ in place of $118$), and neither is anything in the sections *What is borrowed* and *What appears to be new*,
such as the consequence of de Caen's theorem.

## Correspondence with the Lean file

| Text | Lean name (`Erdos1066.lean`) |
|---|---|
| Lemma 1(a), (b) | `card_le`, `gDim_le` |
| Lemma 2 | `eq_of_sq_add_sq` |
| Lemma 3: group $W$; (a), (b) | `W`, its `AddCommGroup` and `Finite` instances; `exists_char`, `sum_char` |
| Lemma 3(c): $u+iv$; $\chi(-p)=\overline{\chi(p)}$ | `char_value`; Mathlib's `AddChar.map_neg_eq_conj` |
| Lemma 4: $\delta$, (2); (a), (b), (c) | `diff`, `diff_add`; `sum_diff_eq_zero`, `normSq_sum_diff`, `re_sum_diff` |
| Lemma 5: vectors, dimension, formula; (a), (b) | `vec`, `finrank_vec`, `inner_vec`; `vec_self`, `vec_ne` |
| Theorem, Corollary | `gDim_upper`, `main` |

All names except `main` are in the namespace `Sol1066`; the coordinate lemmas for `W` are not listed. Lean defines $W$
over every field, with $-(a,b)=(-a,-b+a^2)$, and has $c-c'$, $b-b'$ for $c+c'$, $b+b'$. In characteristic $2$ this is
the same.
