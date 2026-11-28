# Erdős Problem 1066 in higher dimensions: no uniform lower bound $c\,n/d$

## The theorem

Place $n$ non-overlapping spheres of diameter $1$ in $d$-dimensional Euclidean space and look at their centers: a set of $n$ points in $\mathbb{R}^d$ with all pairwise distances at least $1$. Some pairs of spheres may touch (their centers are at distance *exactly* $1$). How many points can we always keep so that *no* two kept spheres touch — that is, every remaining pairwise distance is strictly greater than $1$?

Formally, let $g_d(n)$ be the largest $k$ such that every set of $n$ points in $\mathbb{R}^d$ with pairwise distances at least $1$ contains $k$ points with pairwise distances strictly greater than $1$. In graph-theoretic terms, if we connect two points by an edge whenever their distance is $1$, then $g_d(n)$ is the smallest possible *independence number* (size of a largest subset with no edges between them) of such a unit-distance graph on $n$ vertices in $\mathbb{R}^d$. Problem 1066 itself asks for the size of $g_2(n)$; this writeup does not address the planar case.

R. Pollack (J. Combin. Theory Ser. A 40 (1985) 450) quotes a letter in which "Erdős asks for a proof or disproof of $f(n,k)>cn/k$". In his notation $f(n,k)$ is $g_k(n)$, where $k$ is the dimension and $n$ is the number of points. We interpret $c>0$ as an absolute constant that depends on neither the dimension nor $n$. This matches the Formal Conjectures statement (`Erdos1066.erdos_1066.variants.higher_dim`), whose negation we prove in Lean. Under this interpretation the answer is no.

**Theorem.** Let $A=2^m$ for an integer $m\ge 0$, and set $d=6A^2$ and $n=4A^4$. Then $g_d(n)\le 2A+2$.

**Corollary.** There is no $c>0$ such that $g_d(n)\ge c\,n/d$ for all $d\ge 1$ and all $n\ge 0$.

*Proof of the Corollary.* If such a $c>0$ existed, applying it to the parameters in the Theorem would give
$$\tfrac{2}{3}cA^2 = c\cdot\frac{4A^4}{6A^2} \le 2A+2 \le 4A,$$
so $cA\le 6$ for every $A=2^m$. This fails for large $m$. $\blacksquare$

The Corollary disproves even the non-strict form of Erdős's inequality, and the same holds if we consider only large $n$ (see the remark on *Large $n$* below).

The vectors constructed below are not new. The Corollary already follows from Lemma 1 together with a theorem of D. de Caen (2000) on *equiangular lines* (lines through the origin in $\mathbb{R}^d$ that all make the same acute angle with one another), quoted in the section *What is borrowed*; a reader willing to assume that theorem can stop after Lemma 1. Lemmas 2 to 5 give a self-contained construction.

## Idea of the proof

A naive lower bound on the number of touching pairs comes from packing disjoint regular simplices of side length $1$ (each having $d+1$ vertices in $\mathbb{R}^d$), where at most $1$ vertex per simplex can be kept; that only yields $g_d(n) \le \lceil n/(d+1) \rceil$, which is still of order $n/d$. To crush $cn/d$, we need *far more than $d$* points in $\mathbb{R}^d$ packed so tightly on a sphere that no large subset can avoid the minimum distance.

The proof has two clean halves:

1. **A two-line norm argument (Lemma 1).** Suppose we have $n$ vectors in $\mathbb{R}^d$ of common squared length $L$ whose pairwise inner products take only two values: $+A$ and $-A$. Because $\lVert w_j - w_l \rVert^2 = 2L - 2\langle w_j, w_l \rangle$, there are at most two pairwise distances, and inner product $+A$ gives the smaller one (which rescales to distance $1$).

   Now take any $k$ vectors whose pairwise distances are all strictly greater than $1$. Every pair among them must have inner product $-A$, meaning they all point slightly *away* from one another. You cannot pack too many mutually obtuse vectors into any Euclidean space, regardless of dimension: expanding the non-negative squared norm of their sum gives
   $$0 \le \Big\lVert\sum w\Big\rVert^2 = kL - k(k-1)A,$$
   which forces $k \le 1 + L/A$. In our construction $L = 2A^2 + A$, yielding $k \le 2A + 2$. Crucially, $k$ grows only like $A = \Theta(\sqrt{d})$, while we will construct $n = 4A^4 = \Theta(d^2)$ vectors — making $n/d = \Theta(A^2)$ overwhelm $k$.

2. **Building $4A^4$ vectors in $\mathbb{R}^{6A^2}$ (Lemmas 2–5).** How do we get quadratically many vectors whose pairwise inner products are strictly $\pm A$? Start with the finite field $F$ having $q = 2A^2 = 2^{2m+1}$ elements, and equip $W = F \times F$ with a "twisted" addition (generalizing binary addition with a carry bit modulo $4$). Using a character $\chi : W \to \mathbb{C}^\times$, we define $q^2 = 4A^4$ complex functions $x \mapsto \chi(cx, bx)$ indexed by pairs $(c, b) \in F \times F$:
   * **Same block ($c = c'$, $b \ne b'$):** the two functions are orthogonal, so their inner product is $0$.
   * **Different blocks ($c \ne c'$):** the complex inner product $S$ satisfies $|S|^2 = q = 2^{2m+1}$ and has integer real and imaginary parts, which forces $\operatorname{Re} S = \pm A$ (Lemma 2).

   That gives real inner products in $\{0, +A, -A\}$ — almost what we need, except for the $0$s within each block. To repair those $0$s without disturbing different blocks, we append $q$ real coordinates (one slot for each $c \in F$) and place $\sqrt{A}$ in slot $c$ of every vector in block $c$. That bumps every same-block inner product from $0$ to $+A$, bumps every squared length from $q = 2A^2$ to $2A^2 + A$, and leaves different-block inner products untouched at $\pm A$.

## Lemma 1 (vectors with inner products $\pm A$)

*Why we need this lemma:* It converts our geometric problem about $g_d(n)$ into a purely algebraic target — finding $n$ vectors of squared norm $2A^2+A$ whose pairwise inner products lie in $\{+A, -A\}$.

Let $A\ge 1$ be an integer, and let $w_1,\dots,w_n$ be vectors in a real inner product space of dimension $d$ with $\lVert w_j\rVert^2=2A^2+A$ and $\langle w_j,w_l\rangle\in\{A,-A\}$ for all $j\ne l$.

(a) If $k$ of these vectors have all pairwise inner products equal to $-A$, then $k\le 2A+2$.

(b) $g_d(n)\le 2A+2$.

*Proof.* (a) We may assume $k\ge 1$. Summing $w$ over these $k$ vectors and expanding the squared norm gives
$$0\le\Big\lVert\sum w\Big\rVert^2=k(2A^2+A)-k(k-1)A=kA\,(2A+2-k).$$
Dividing by $kA>0$ yields $k\le 2A+2$.

(b) Identify the ambient space with $\mathbb{R}^d$ and rescale each vector by setting $p_j=w_j/(2A)$. For every $j\ne l$,
$$\lVert p_j-p_l\rVert^2=\frac{2(2A^2+A)-2\langle w_j,w_l\rangle}{4A^2}=1+\frac{A-\langle w_j,w_l\rangle}{2A^2}.$$
Evaluating the two possible inner products gives:
* $\lVert p_j - p_l \rVert^2 = 1$ when $\langle w_j, w_l \rangle = A$;
* $\lVert p_j - p_l \rVert^2 = 1 + 1/A > 1$ when $\langle w_j, w_l \rangle = -A$.

The $n$ points $p_j$ are therefore distinct, all pairwise distances are at least $1$, and a pair has distance strictly greater than $1$ only when the corresponding vectors have inner product $-A$. By (a), at most $2A+2$ points can have all pairwise distances strictly greater than $1$. $\blacksquare$

## Lemma 2 (two squares)

*Why we need this lemma:* In Lemma 4, each cross-block character sum $S = U + iV$ will be a Gaussian integer (integer real and imaginary parts) with $U^2 + V^2 = 2^{2m+1}$. This quick parity descent shows that its real part $U$ has no choice but to be $\pm 2^m = \pm A$.

Let $u,v$ be integers with $u^2+v^2=2^{2m+1}$ for an integer $m\ge 0$. Then $u=\pm 2^m$.

*Proof.* We induct on $m$.
* **Base case ($m = 0$):** Here $u^2+v^2=2$, so $u=\pm 1$.
* **Inductive step ($m \ge 1$):** Every integer square is congruent to $0$ or $1$ modulo $4$ depending on whether its root is even or odd. Since $4\mid 2^{2m+1} = u^2+v^2$, neither $u$ nor $v$ can be odd, so both $u$ and $v$ are even. Dividing by $4$ gives
  $$\left(\frac{u}{2}\right)^2+\left(\frac{v}{2}\right)^2=2^{2(m-1)+1}.$$
  By the induction hypothesis, $u/2=\pm 2^{m-1}$, and hence $u=\pm 2^m$. $\blacksquare$

## Lemma 3 (the group $W$ and its characters)

*Why we need this lemma:* We want complex-valued functions whose inner products have integer real and imaginary parts (so Lemma 2 applies). Characters taking values in $\{1, -1, i, -i\}$ guarantee this, which calls for an abelian group of exponent $4$ built from our characteristic-$2$ field $F$.

*Intuition for the group law:* In base-$2$ arithmetic modulo $4$, adding two $2$-bit numbers $(a, b)$ and $(a', b')$ produces a low bit $a + a' \pmod 2$ and a high bit $b + b' + aa' \pmod 2$, where $aa'$ is the carry from the low bit. The group $W = F \times F$ below uses the exact same "carry" rule over an arbitrary finite field $F$ of characteristic $2$.

From now on $A=2^m$, and $F$ is the finite field with $q=2^{2m+1}=2A^2$ elements. Since $F$ has characteristic $2$, we have $t+t=0$ (so $-t=t$) for all $t\in F$. Let $W=F\times F$ with addition defined by
$$(a,b)+(a',b')=(a+a',\;b+b'+aa').$$
This operation makes $W$ an abelian group:
* it is commutative and associative (both ways of grouping three elements give $(a+a'+a'',\,b+b'+b''+aa'+aa''+a'a'')$);
* the zero element is $(0,0)$;
* the additive inverse is $-(a,b)=(a,\,b+a^2)$.

We will frequently use two special cases of these formulas:
$$(a,b)+(0,t)=(a,b+t),\qquad -(0,t)=(0,t).\tag{1}$$
A *character* of $W$ is a homomorphism $\chi$ from $W$ to the multiplicative group of nonzero complex numbers, so $\chi(p+p')=\chi(p)\chi(p')$ and $\chi(-p)=1/\chi(p)$. We write $\chi(a,b)$ for $\chi((a,b))$.

(a) There is a character $\chi$ of $W$ with $\chi(0,1)\ne 1$. Fix such a $\chi$.

(b) If $t\in F$ is nonzero, then $\sum_{x\in F}\chi(0,tx)=0$.

(c) For every $p\in W$, we have $\chi(p)=u+iv$ for integers $u,v$ (with $i=\sqrt{-1}$), and $\chi(-p)=\overline{\chi(p)}$.

*Proof.*
(a) Every nonzero element $p$ of a finite abelian group admits a character with $\chi(p)\ne 1$ (a standard fact).

(b) Let $T=\sum_{x\in F}\chi(0,tx)$. Because $t \ne 0$, the map $x \mapsto x + 1/t$ permutes $F$, and by (1),
$$(0,t(x+1/t))=(0,tx+1)=(0,tx)+(0,1).$$
Shifting $x$ to $x+1/t$ therefore multiplies every term of $T$ by $\chi(0,1)$, giving $T=\chi(0,1)\,T$. Since $\chi(0,1)\ne 1$, we conclude $T=0$.

(c) Direct calculation in characteristic $2$ gives $2(a,b)=(a+a,\,b+b+a^2)=(0,a^2)$, and adding $(0,a^2)$ to itself gives $4(a,b)=(0,0)$. Therefore $\chi(p)^4=\chi(0)=1$, so $\chi(p)\in\{1,-1,i,-i\}$. In particular, $\chi(p)$ has integer real and imaginary parts and $|\chi(p)|=1$, which gives $\chi(-p)=1/\chi(p)=\overline{\chi(p)}$. $\blacksquare$

*Sanity check ($m = 0$, $A = 1$, $q = 2$):* Here $F = \mathbb{F}_2 = \{0, 1\}$, and $W = \mathbb{F}_2 \times \mathbb{F}_2 \cong \mathbb{Z}/4\mathbb{Z}$ with generator $(1, 0)$ since $2(1,0) = (0,1)$ and $4(1,0) = (0,0)$. Viewing $a, b \in \{0, 1\}$ as integers, $\chi(a,b) = i^{a + 2b}$ is a character with $\chi(0,1) = -1 \ne 1$, all values lie in $\{1, -1, i, -i\}$, and $\sum_{x \in \mathbb{F}_2} \chi(0, x) = 1 + (-1) = 0$.

## Lemma 4 (the character sums)

*Why we need this lemma:* Each of our vectors will have complex part $\big(\chi(cx, bx)\big)_{x \in F}$. The complex inner product between the $(c,b)$-vector and the $(c',b')$-vector is precisely the character sum $S$ below. Notice how the quadratic carry term in $W$ pays off in part (b): when $c \ne c'$, the carry injects a bilinear term $(0, e^2 yx)$ into $\delta(x+y) - \delta(x)$, causing all off-diagonal terms in $|S|^2$ to cancel cleanly by Lemma 3(b).

Let $c,b,c',b'\in F$ (here $c$ is a field element, unrelated to the constant in the Corollary) and define
$$\delta(x)=(cx,bx)-(c'x,b'x)\in W\quad(x\in F),\qquad S=\sum_{x\in F}\chi(\delta(x)).$$

(a) If $c=c'$ and $b\ne b'$, then $S=0$.

(b) If $c\ne c'$, then $|S|^2=q$.

(c) If $c\ne c'$, then $\operatorname{Re}S=\pm A$.

*Proof.*
(a) By (1), $(cx,bx)=(cx,0)+(0,bx)$ and $(cx,b'x)=(cx,0)+(0,b'x)$. Subtracting cancels $(cx,0)$ and gives
$$\delta(x)=(0,bx)-(0,b'x)=(0,(b+b')x).$$
Since $b\ne b'$, we have $b+b'\ne 0$, and Lemma 3(b) gives $S=0$.

(b) Set $e=c+c'\ne 0$. By the definition of addition in $W$ and (1), the carry when adding $(cx, bx)$ and $(cy, by)$ is $c^2 yx$, so
$$(cx+cy,\,bx+by)=(cx,bx)+(cy,by)+(0,c^2yx).$$
Subtract the same identity for $c', b'$. Using (1) and the characteristic-$2$ identity $c^2+c'^2=(c+c')^2=e^2$ gives
$$\delta(x+y)=\delta(x)+\delta(y)+(0,e^2yx).\tag{2}$$
Now expand $|S|^2 = S\,\overline{S}$. Reindex the first summation variable as $x+y$ and the second as $x$, then apply Lemma 3(c) ($\overline{\chi(\delta(x))} = \chi(-\delta(x))$) and (2):
$$|S|^2=\sum_{x,y}\chi(\delta(x+y))\,\overline{\chi(\delta(x))}=\sum_{x,y}\chi(\delta(x+y)-\delta(x))
=\sum_{y}\chi(\delta(y))\sum_{x}\chi(0,e^2y\,x).$$
Evaluate the inner sum over $x \in F$:
* When $y\ne 0$, we have $e^2 y \ne 0$, so the inner sum vanishes by Lemma 3(b).
* When $y=0$, every term of the inner sum is $\chi(0,0)=1$, so the inner sum equals $q$, and the outer factor is $\chi(\delta(0))=\chi(0,0)=1$.

Therefore $|S|^2=q$.

(c) By Lemma 3(c), each term $\chi(\delta(x))$ has integer real and imaginary parts, so $S=U+iV$ for integers $U,V$. Part (b) says $U^2+V^2=q=2^{2m+1}$. Lemma 2 then gives $U=\pm 2^m=\pm A$. $\blacksquare$

*(Continuing our $m = 0$ check: with $\chi(a,b) = i^{a+2b}$, taking $(c,b)=(1,0)$ and $(c',b')=(0,0)$ gives $\delta(0)=(0,0)$ and $\delta(1)=(1,0)$, so $S = 1 + i$, $|S|^2 = 2 = q$, and $\operatorname{Re} S = 1 = +A$.)*

## Lemma 5 (the vectors)

*Why we need this lemma:* We now assemble the actual vectors in a real inner product space of dimension $3q = 6A^2$. Viewing $\mathbb{C}^q$ as $\mathbb{R}^{2q}$ gives real inner products $\operatorname{Re} S \in \{0, +A, -A\}$; appending $\mathbb{R}^q$ with a single spike of height $\sqrt{A}$ in slot $c$ lifts the same-block $0$s to $+A$ without touching cross-block inner products.

We work in $\mathbb{C}^q\oplus\mathbb{R}^q$, with coordinates indexed by $F$. This is a real inner product space of dimension $3q$ under
$$\langle(z,s),(z',s')\rangle=\operatorname{Re}\sum_{x\in F}z_x\overline{z'_x}+\sum_{x\in F}s_xs'_x.$$
For $c,b\in F$, let $w_{c,b}$ be the vector whose first part is $\big(\chi(cx,bx)\big)_{x\in F}$ and whose second part has $\sqrt A$ in coordinate $c$ and $0$ everywhere else.

(a) $\lVert w_{c,b}\rVert^2=2A^2+A$.

(b) If $(c,b)\ne(c',b')$, then $\langle w_{c,b},w_{c',b'}\rangle=\pm A$.

*Proof.* By Lemma 3(c), $\chi(cx,bx)\,\overline{\chi(c'x,b'x)}=\chi(\delta(x))$. With $S$ as in Lemma 4, the inner product splits into the character sum plus the contribution of the $\sqrt{A}$ spikes:
$$\langle w_{c,b},w_{c',b'}\rangle=\operatorname{Re}S+\begin{cases}A&\text{if }c=c',\\0&\text{if }c\ne c'.\end{cases}$$

(a) When $(c,b)=(c',b')$, we have $\delta(x)=0$ for all $x$, so $S=q=2A^2$, and the formula gives $2A^2+A$.

(b) When $c=c'$ and $b\ne b'$, Lemma 4(a) gives $S=0$, so the inner product is $0 + A = A$. When $c\ne c'$, the real spikes sit in different coordinates and contribute $0$, while Lemma 4(c) gives $\operatorname{Re}S=\pm A$. $\blacksquare$

## Proof of the Theorem

Lemma 5 produces $q^2=4A^4$ vectors $w_{c,b}$ (one for each pair $(c,b) \in F \times F$) in a real inner product space of dimension $3q=6A^2$ satisfying all hypotheses of Lemma 1. Applying Lemma 1(b) gives $g_{6A^2}(4A^4)\le 2A+2$. $\blacksquare$

## Remarks

* *All dimensions.* Because $\mathbb{R}^d\subset\mathbb{R}^{d'}$ for $d\le d'$, $g_d(n)$ is nonincreasing in $d$. For $d\ge 6$, pick the power of two $A$ with $6A^2\le d<24A^2$ and set $n=4A^4$. Then
  $$g_d(n)\le 2A+2\le 4A=\frac{n}{A^3}\le \frac{24^{3/2}\,n}{d^{3/2}}.$$
  For $d<6$, the bound holds with $n=1$. Thus for every $d\ge 1$ there exists $n\ge 1$ with $g_d(n)\le 118\,n/d^{3/2}$.
* *Large $n$.* Place $N$ copies of an $n$-point set far apart (so distances between distinct copies exceed $1$). If at most $k$ points can be kept from one copy, then at most $Nk$ can be kept from all $N$ copies combined, so $g_d(Nn)\le N\,g_d(n)$. The bound $118\,n/d^{3/2}$ therefore holds for every $d\ge 1$ and arbitrarily large $n$. Likewise, the Theorem gives $g_{6A^2}(4A^4N)\le(2A+2)N$ for all $N\ge 1$. Just as in the proof of the Corollary, there is no $c>0$ such that, for every $d\ge 1$, $g_d(n)\ge c\,n/d$ holds for all sufficiently large $n$.
* *Small dimension.* Disjoint regular simplices of side length $1$ (each with at most $d+1$ vertices) placed far apart give $g_d(n)\le\lceil n/(d+1)\rceil$, since at most one vertex of each simplex can be kept. Our Theorem beats this bound starting at $A=4$ ($10$ versus $11$ for $n=1024$, $d=96$), because $4A^4>(2A+2)(6A^2+1)$ for $A\ge 4$. At $A=4$, however, two configurations cited below pack more points into a smaller dimension while still keeping at most $10$: $1460$ points in $\mathbb{R}^{73}$ (Ismailescu, Lee, and Lee) and $2048$ points in $\mathbb{R}^{95}$ (de Caen). The ratio $n/(2d)$ that Ismailescu, Lee, and Lee attain for other $n$ and $d$ evaluates to $A^2/3$ at our Theorem's parameters, which exceeds $2A+2$ from $A=8$ onward.
* *Limits of the result.* We do not claim that the exponent $3/2$ is optimal. If $c$ is allowed to depend on $d$, then $g_d(n)\ge c\,n/d$ is trivially true: any point has at most $\kappa_d$ neighbors at distance exactly $1$ (where $\kappa_d$ is the kissing number — the maximum number of non-overlapping unit spheres that can touch a central unit sphere in $\mathbb{R}^d$), so a greedy choice keeps at least $n/(\kappa_d+1)$ points.

The proof and its remarks end here. The remaining sections cover sources, priority, and the Lean formalization.

## What is borrowed

### The vectors

D. de Caen (*Large equiangular sets of lines in Euclidean space*, Electron. J. Combin. 7 (2000) R55) constructed $\frac{2}{9}(d+1)^2$ unit vectors in $\mathbb{R}^d$, for $d=3\cdot 2^{2t-1}-1$, with all pairwise inner products equal to $\pm 1/(2^t+1)$. Setting $A=2^{t-1}$ and scaling these vectors by $\sqrt{A(2A+1)}$ produces $8A^4$ vectors in $\mathbb{R}^{6A^2-1}$ with $\lVert w\rVert^2=2A^2+A$ and pairwise inner products $\pm A$. Lemma 1 then yields $g_{6A^2-1}(8A^4)\le 2A+2$: twice as many points as in our Theorem, in one fewer dimension. The Corollary is therefore an immediate consequence of a published theorem.

### The construction

Lemma 4 builds *mutually unbiased bases* of $\mathbb{C}^q$: for each fixed $c$, the $q$ vectors $\big(\chi(cx,bx)/\sqrt q\big)_{x\in F}$ ($b\in F$) form an orthonormal basis of $\mathbb{C}^q$ by Lemma 4(a), and vectors from distinct bases have inner product of modulus $1/\sqrt q$ by Lemma 4(b). Greaves, Koolen, Munemasa, and Szöllősi (*Equiangular lines in Euclidean spaces*, arXiv:1403.2155, Theorem 2.5) obtain de Caen's parameters from mutually unbiased bases of $\mathbb{R}^N$ ($N=4A^2$, meaning orthonormal bases whose cross inner products are $\pm 1/\sqrt N$) by appending extra coordinates as in Lemma 5. Such bases come from Kerdock sets (Kerdock 1972; Cameron and Seidel 1973; Calderbank, Cameron, Kantor, and Seidel 1997). The group $W$ is the additive group of Witt vectors of length two over $F$, used in the $\mathbb{Z}/4$ description of Kerdock codes by Hammons, Kumar, Calderbank, Sloane, and Solé (1994).

## What appears to be new

Only a connection, and only part of it. Lemma 1 is already used in effect for one special line system by Ismailescu, Lee, and Lee (arXiv:2611.23767, 18 November 2026): they take the points $\pm v$ for $r^3+1$ unit vectors in dimension $r^2-r+1$ with inner products $\pm 1/r$ (Taylor's regular two-graphs) and bound the number of points kept using the same norm-of-the-sum argument. They do not mention equiangular lines or de Caen, and that system yields only $n/(2d)$.

We did not find a source noting that large equiangular line systems apply in general (lowering $n/d$ to order $n/d^{3/2}$), nor any published answer to Erdős's question. A May 2026 GitHub repository, `Dr-How/chromatic-sphere-packing` (a generated draft), conjectures the opposite: that the chromatic number of unit-ball contact graphs is $O(d)$, which it states is equivalent to keeping at least $n/(Cd)$ points. Our Theorem refutes the second statement, and hence the first as well.

Every published family of upper bounds on $g_d(n)$ for growing $d$ that we found is of order $n/d$. Examples include:

* $\lceil n/(d+1)\rceil$ from regular simplices;
* $6n/(6d+7)$ for suitable $n$ (Pach; Graham and Chung, in Pollack's note);
* $n/(r^3+1)$ for $n=(r+1)(r^3+1)$ and $d=r^3-r^2+r$, where $r$ is a prime power (H. Chen, arXiv:1502.02070);
* $n/(2d)$ for $n=2(r^3+1)$ and $d=r^2-r+1$, where $r$ is an odd prime power (Ismailescu, Lee, and Lee, arXiv:2611.23767).

The last two results are stated as lower bounds on chromatic numbers, but their proofs lower-bound $n/k$, where $k$ is the maximum number of points that can be kept. G. Kalai's survey (arXiv:1505.04952) discusses both de Caen's theorem (Theorem 2.6) and a question on minimum-distance graphs (Problem 5.1) without connecting them, so experts may already know this observation.

Our three literature searches on 24-25 November 2026 (the third specifically using the vocabulary of equiangular lines) were limited. The main unread source is Bezdek, Naszódi, and Visy (*On the mth Petty numbers of normed spaces*, 2003). We also did not read the problem page or its four-post forum thread on the Erdős problems site. Another site's entry for the problem, https://www.erdosproblemaday.com/problem/1066 (dated 29 July 2026), lists it as open and mentions that the official page then showed "a claimed proof or a listed worker", with no further details, so we do not know what that refers to.

This writeup and the Lean proof were generated by an AI agent and machine-checked in Lean; they have not been reviewed by a human expert. The Theorem, Corollary, and Lemmas 1 to 5 are machine-checked. The Remarks are not (an earlier Lean proof established the bound in *All dimensions* with $2^{21}$ in place of $118$), and neither is anything in *What is borrowed* or *What appears to be new*, including the deduction from de Caen's theorem.

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

All names except `main` live in the namespace `Sol1066`; helper lemmas for the coordinates of `W` are omitted from the table. Lean defines $W$ over an arbitrary field with $-(a,b)=(-a,-b+a^2)$ and writes $c-c'$, $b-b'$ in place of $c+c'$, $b+b'$. In characteristic $2$, these agree.
