# Erdős problem 160 and colorings of four-term arithmetic progressions

Color the integers $[N] = \{1, 2, \dots, N\}$ so that **every four-term arithmetic progression (4-AP)** — four equally spaced numbers $a, a+d, a+2d, a+3d$ with common difference $d > 0$ — displays **at least three distinct colors**. Let $h(N)$ denote the minimum number of colors needed.

Erdős and Freud asked how fast $h(N)$ grows ([Problem #160](https://www.erdosproblems.com/160)). Right now, the frontier sits at **$N = 78$**: Scott Schluer's certificate rules out 6 colors already at $[54]$ ([six-color exclusion](https://github.com/scottschluer/erdos160/tree/c5745c8e359e4f0602382c18bc512c0e9559207b/results/erdos160-small-values)), while Arhan Canli found a valid 7-coloring of $[77]$ ([Canli's witness](https://github.com/arhancanli/quantavane-erdos-results/blob/6a4c61d4b873f9cccc66c903993d319d3d2c1250/160/witness/k7_N77.txt)). Appending color 4 to Canli’s word and giving position 3 a fresh color yields an eight-coloring of $[78]$. Thus $h(78)$ is **either 7 or 8**. [Verification of the eight-coloring](#3-edit-distance-from-canlis-77-position-coloring)

## The asymptotic growth exponent exists

Use $[0,N)=\{0,\ldots,N-1\}$. Write $H(m)$ for the same minimum on the
circle of residues modulo an odd $m\ge3$, allowing every nonzero step.
Then

$$
\lim_{N\to\infty}\frac{\log h(N)}{\log N}
=\alpha
=\inf_{\substack{m\ge3\\m\ \mathrm{odd}}}\frac{\log H(m)}{\log m}.
$$

**1. Detect a wrap in three terms.** Let $b(t)=\lfloor\log_2 t\rfloor$ for
$t\ge1$. Take an optimal interval coloring of $[0,m)$ and attach to each
color at $x$ the tag
$$
(x\bmod2,\ b(x+1),\ b(m-x)).
$$
A modular triple $x,y,z$ satisfies $x+z=2y$ or $x+z=2y\pm m$.
In the plus case the endpoints have opposite parity, since $m$ is odd.
Also $x,z\ge2y+1$, since each endpoint is at most $m-1$. Thus both
endpoints have a larger $b(\,\cdot+1)$ label than the middle. All three
tags differ. Reflection $x\mapsto m-1-x$ gives the minus case by
interchanging the two logarithmic labels.

Consequently, if a cyclic four-term progression used at most two refined
colors, each of its two consecutive triples would be an ordinary arithmetic
progression. Their common middle pair gives them the same step. All four
representatives would then form an ordinary progression of nonzero step,
contradicting the interval coloring. Counting the possible tags gives
$$
H(m)\le 2(1+\lfloor\log_2m\rfloor)^2h(m).
$$

Lean checks the claim for both three and four terms. [ShortLift.lean](ShortLift.lean)

**2. Repeat the coloring on digits.** Color each integer in $[0,m^k)$
by the tuple of cyclic colors of its $k$ base-$m$ digits. For a progression
of positive step $d$, let $j$ be the largest integer with $m^j\mid d$.
Adding $d$ leaves the bottom $j$ digits fixed, and digit $j$ advances by
$d/m^j\not\equiv0\pmod m$ (digit zero is the units digit). That digit
alone shows three colors. Rounding $N$ up to the next power of $m$ gives
$$
h(N)\le H(m)^{\lceil\log_mN\rceil}.
$$

For each fixed odd $m$, the last inequality gives
$\limsup_{N\to\infty}\log h(N)/\log N\le\log H(m)/\log m$.
Taking the infimum gives the upper bound $\alpha$. For the lower bound
take the largest odd $m\le N$. By step 1 and the definition of $\alpha$,
$m^\alpha\le H(m)\le 2(1+\lfloor\log_2m\rfloor)^2h(N)$.
Here $m\ge N-1$, and the logarithm of the extra factor is
$O(\log\log N)$. Dividing by $\log N$ proves that the lower limit is
at least $\alpha$. This proves convergence. [Lean theorem](GrowthLimit.lean)

In particular, $h(N)=N^{\alpha+o(1)}$ with $0\le\alpha\le1/4$.
The upper endpoint follows from Shi and Dong. The value of $\alpha$ is
unknown. [Shi and Dong, Corollaries 1.2 and 1.3](https://arxiv.org/html/2607.20752v2)

### A uniform twelve-label bound

For every odd $m$, one has $h(m)\le H(m)\le12h(m)$. The first inequality
follows by restriction. For the second, attach the following tag to the old
color of the digit $x$:

$$
T_m(x)=\left(x\bmod2,\ {\bf1}_{2x<m},\
\left\lfloor\log_2\big(1+2\min(x,m-1-x)\big)\right\rfloor\bmod3\right).
$$

Consider a cyclic progression with representatives $x_0,x_1,x_2,x_3$.
There are four cases for a failure of the refined coloring. Letters below
denote equalities within pairs, and may themselves agree.

* **ABAB.** Both second differences are divisible by $m$. Both are even
  because their endpoints have equal parity. Their absolute values are
  strictly less than $2m$, so both vanish. The representatives form an
  ordinary integer progression.
* **ABBA.** The same divisibility by $2m$ holds for
  $x_0+x_3-x_1-x_2$ and $(x_3-x_0)-3(x_2-x_1)$. The first has absolute
  value less than $2m$. In the second, each matched pair is in the same
  half, so its absolute value is at most $4(m-1)/2<2m$. Both expressions
  vanish. These two equations make the three successive differences equal.
* **AABB.** The two outer increments are congruent modulo $m$ and have
  absolute value at most $(m-1)/2$. Thus they are equal as integers. Reverse
  the progression if needed so that their common value $s$ is positive.
  The only possible unequal middle increment is $s-m$. In that case
  $x_1\ge m-s$ and $x_2<s$, putting the first pair in the upper half and
  the last pair in the lower half. Put $B=m-\tfrac12-x_1$ and
  $C=x_2+\tfrac12$. Then $B+C=s$. The distances of the four digit midpoints
  to their nearer endpoint of $[0,m]$ are respectively $B+s,B,C,C+s$.
  For $u=\max(B,C)$ one has $2<(u+s)/u\le3$. Thus the dyadic exponents
  of $2u$ and $2(u+s)$ differ by one or two. This contradicts their
  matching tags.
* **Three equal colors** at $i<j<k$. The quantity
  $D=(k-j)x_i-(k-i)x_j+(j-i)x_k$ is divisible by $m$ and even.
  Since the three representatives share a half,
  $|D|\le 3(m-1)/2<2m$. Hence $D=0$.
  The three indices include adjacent indices, so the points lie at their
  prescribed indices on an integer progression of nonzero integral step.
  If $k-i=3$, the fourth point lies between the two endpoints. Otherwise the
  three points in increasing order are $v,v+t,v+2t$. They share a half,
  so $4t\le m-1$. If $v<t$, then $v+3t\le m-1$. If $v\ge t$, we may use
  $v-t$. In either case an ordinary four-term progression contains the triple.

In each case an ordinary four-term progression has at most two of the old
colors, contradicting the initial coloring. The cyclic step may be
noninvertible modulo $m$. The proof only needs it to be nonzero.
Lean checks the transfer for all odd moduli. [CyclicTransfer.lean](CyclicTransfer.lean)

Using $12$ in place of the logarithmic factor gives the pointwise bound
$h(N)\ge(N-1)^\alpha/12$ for $N\ge2$. The digit argument also gives
$H(mn)\le H(m)H(n)$ for odd $m,n$, by writing $x=r+mq$ and pairing the
cyclic colors of $r$ and $q$. [Cyclic products](CyclicProduct.lean),
[minima](PaletteMinima.lean), [formal limit and pointwise bound](GrowthLimit.lean)

An unconditional lower bound comes from three-term progressions. Put
$M=\lfloor 2N/3\rfloor$. Any monochromatic $a,a+d,a+2d$ in $[0,M)$
extends to $a+3d<N$. Thus each color has at most $r_3(M)$ members in
$[0,M)$, where $r_3(M)$ is the largest size of a three-term progression-free
subset. Raghavan's estimate gives
$h(N)\ge M/r_3(M)\ge\exp(c(\log N)^{1/6}/\log\log N)$ for some $c>0$
and all sufficiently large $N$. [Raghavan, *Improved Bounds for 3-Progressions*](https://arxiv.org/abs/2603.27045)

### An explicit bound for the cost of the nonsymmetric patterns

Let $s(N)$ count the colors needed when only **ABBA** is forbidden, meaning
that the first and last colors agree and the middle two agree. For odd $M\ge3$
and $k\ge1$ with $M^k\ge N$, one has

$$
s(N)\le h(N)\le s(N)\,12^k\big(1+k(M-1)^2\big).
$$

Write each integer in $[0,N)$ as a vector $X$ of $k$ base-$M$ digits.
Give it the auxiliary color consisting of the $k$ tags $T_M(X_j)$ and the
integer $\|X\|^2=\sum_j X_j^2$. For ABAB and AABB, matched tags lift the
lowest digits to an integer progression by the proof above. A zero digit
step already gives four identical digits. Subtract the digits and divide
by $M$ to obtain an integer progression of quotients. Iteration shows that
the four digit vectors form an ordinary vector progression $U+iV$.
For three matching colors, apply the relation $D$ above at the three
matched indices. Whenever the relation vanishes on the lower digits, it
holds modulo $M$ on the next digit. The same parity and half bounds give
exact equality there. Thus the three digit vectors also lie on a line
$U+iV$ at the specified indices. In both arguments $V\ne0$ because the
original integers are distinct.

The function $q(t)=\|U+tV\|^2$ is a quadratic with positive leading
coefficient. It cannot take one value three times. If $q(i)=q(j)$ for
$i\ne j$, their midpoint is the axis of the quadratic, so two such equal
pairs must have the same midpoint. This excludes ABAB and AABB. Only ABBA
can survive, and the independent $s(N)$-coloring excludes it. This use of
the squared norm follows the Behrend-type construction in Shi and Dong,
Section 5. The fixed twelve digit labels replace the growing number of
labels in their AABB construction. [Shi and Dong, Section 5](https://arxiv.org/html/2607.20752v2#S5)

Choose an odd $M$ within two of $\exp(\sqrt{\log N})$ and take
$k=\lceil\log_M N\rceil$. Then $k=O(\sqrt{\log N})$, so both $12^k$ and
$1+k(M-1)^2$ are at most $\exp(O(\sqrt{\log N}))$. Thus $s(N)$ has
the same growth exponent as $h(N)$, and Shi and Dong's bound
$s(N)=O(N^{1/4})$ gives
$$h(N)\le N^{1/4}\exp(O(\sqrt{\log N})).$$
[Shi and Dong, Theorem 1.1 and Corollary 1.2](https://arxiv.org/html/2607.20752v2)

**Refining the constant.** Ten digit labels suffice for the same auxiliary coloring. For midpoint
$v=x+\tfrac12>M/2$ keep parity and the dyadic band (six labels).
For $v<M/3$ keep only the band (three separate labels). Use one more
label on $M/3\le v\le M/2$. For a matched triple in either lower region,
the diameter is less than $M/3$, so $|D|<M$ and divisibility by $M$
suffices. The upper region retains the parity argument.
For ABAB the two displacements $x_2-x_0$ and $x_3-x_1$ are congruent
modulo $M$, and both have absolute value at most $(M-1)/2$, so they agree
as integers. If either pair is in the upper half, its displacement is even
and hence both displacements are even. Both second differences are then
even multiples of $M$ in absolute value less than $2M$, so they vanish.
If both pairs are in the lower half,
all four digits lie within a single half, so their three successive
increments are equal as integers. For AABB the previous wrap argument
still applies unless the lower pair is in the middle strip
$[M/3,M/2]$. There its displacement would satisfy $s\le M/6$ while
its smaller midpoint $C$ satisfies $M/3\le C<s$, which is impossible.

Taking $M$ to be an odd integer within two of
$\exp(\sqrt{(\log10)(\log N)/2})$ and $k=\lceil\log_M N\rceil$ gives

$$
0\le\log\frac{h(N)}{s(N)}
\le 2\sqrt{2(\log10)(\log N)}+O(\log\log N).
$$

All unmarked logarithms are natural.

This gives a finite criterion for improving the leading exponent. Write
$S(m)$ for the least number of colors forbidding ABBA on every nonzero-step
progression modulo $m$, including even $m$. The cyclic tensor-power rule
for this pattern, followed by restriction, gives
$s(N)\le S(m)^{\lceil\log_m N\rceil}$. Consequently
$\alpha\le\inf_{m\ge2}\log S(m)/\log m$. The reverse inequality follows
from $S(m)\le H(m)$ on odd moduli and the limit formula above. In particular,
$\alpha<1/4$ holds **if and only if** one finite cyclic $r$-coloring
avoids ABBA at a modulus $m>r^4$. [Deng, Tidor and Zhao, Lemma 5.1](https://arxiv.org/html/2307.06914#S5)

One also has $m^\alpha\le S(m)\le3s(m)\le3h(m)$ for every $m\ge2$.
For the middle inequality attach the label $\lfloor3x/m\rfloor$ to each
interval color. Orient the cyclic step forward with size at most $m/2$.
If the middle pair has equal labels, the increment between them is a
positive integer $d<m/3$. If their bin is $j$, the first digit lies in
bin $j$ or $j-1$ and the last in $j$ or $j+1$, with bin indices modulo
three. Equal endpoint labels force both into bin $j$. All four successive
representatives therefore form an ordinary progression. The factor three
is sharp for comparing $S$ and $s$, since $S(3)=3$ and $s(3)=1$.
[Shi and Dong, Lemma 2.1](https://arxiv.org/html/2607.20752v2#S2),
[Lean transfer](SymmetricTransfer.lean), [formal minima and equality case](SymmetricMinima.lean)

The same argument relates $\alpha$ to colorings of vector spaces. For a
prime $p>3$, let $b_p(t)$ be the symmetric-pattern minimum on
$\mathbb F_p^t$. Direct products give $b_p(t+u)\le b_p(t)b_p(u)$, so
$\beta_p=\lim_{t\to\infty}\log b_p(t)/(t\log p)$ exists by subadditivity.
The two inequalities

$$
b_p(t)\le3^t s(p^t),\qquad s(p^t)\le3^{t-1}b_p(t)\quad(t\ge1)
$$

give $|\beta_p-\alpha|\le\log3/\log p$. For the first inequality, read
the vector as a base-$p$ integer and tag every coordinate by its third.
Matched symmetric pairs lift in each coordinate, so the integers are on
a nonconstant ordinary progression. For the second, read the vector of
digits of an integer and tag all but the top digit by their thirds.
Whenever symmetric pairs match, the lowest digits lift to an integer
progression. Subtracting those digits and dividing by $p$ lets the
argument continue one digit up. The resulting field vectors form a
nonconstant progression. This last direction is the digit construction
in Shi and Dong. In particular, $\lim_{p\to\infty}\beta_p=\alpha$ along
the primes. [Shi and Dong, Lemma 2.2](https://arxiv.org/html/2607.20752v2#S2)

For two or three colors, the exact maximum cyclic moduli are **2** and
**22**. The corresponding maximum interval lengths are **14** and **69**.
In fact, *every* three-color cyclic example at modulus 22 is a rotation of
Deng, Tidor and Zhao's word, up to renaming colors. To verify this, enumerate
valid interval words by appending one letter at a time. At position $n$, a
step $d$ forbids the color at $n-3d$ precisely when the colors at $n-d$
and $n-2d$ agree. This tests all progressions ending at $n$. Use names in
order of first appearance. There are 13,193,195 prefixes in the entire
three-color search and eight words of length 69, forming four reversal
classes. A cyclic word of length $m$ repeats to a valid interval word of
length $3m$, so $m\le23$ for three colors. Testing all interval words
of lengths 22 and 23 gives exactly the 22 normalized rotations at length
22 and none at length 23. [Exhaustive verifier](symmetric_bases.cpp)

### Using the cubic construction on the last two digits

The following refinement reduces the coefficient of $\sqrt{\log N}$:

$$
\log h(N)\le \tfrac14\log N+
2\sqrt{\log10}\,\sqrt{\log N}+O(\log\log N).
$$

Let $p>5$ be prime and $Q=p^2$. The auxiliary coloring just constructed on
the interval of length $Q$ can also exclude triples, ABAB and AABB on the
cycle modulo $Q$ at a cost of twelve more labels. Attach $T_Q$ and use
the lifting proof above. In the triple case the three points belong to an
ordinary four-term progression on which the auxiliary coloring forbids
every monochromatic triple. Thus the cyclic cost is at most
$12\cdot10^k(1+k(M-1)^2)$ whenever $M^k\ge Q$.

Write $n\bmod p^4$ as four base-$p$ digits $(x_0,x_1,y,z)$ in increasing
order of significance. Fix a basis $(e_0,e_1,e_2)$ of $\mathbb F_{p^3}$
over $\mathbb F_p$. Give $n$ its three tags $T_p(x_0),T_p(x_1),T_p(y)$,
the auxiliary cyclic color of $n\bmod p^2$, and the field element

$$
F(n)=\operatorname{Norm}(x_0e_0+x_1e_1+ye_2)+z \quad \text{in }\mathbb F_p .
$$

This is the cubic-plus-linear construction of Shi and Dong with the cubic
on the low digits. There is one further tag. Put
$w=(x_0e_0+x_1e_1)/e_2$ and $u=y+\operatorname{Tr}(w)/3$.
On $\mathbb F_p^\times$ join $v$ to $rv$ for
$r\in\{-1,4,3,-3\}$. The undirected graph has maximum degree at most seven
and has a proper coloring with eight colors by the greedy algorithm.
Attach this graph color of $u$ to $n$. At zero use any of the eight colors.
[Shi and Dong, Sections 3 and 4](https://arxiv.org/html/2607.20752v2#S4)

Consider any nonzero cyclic step modulo $p^4$. If all matched pairs are
ABBA, the tags on the first three digits lift them, digit by digit.
Consequently the four field digit vectors lie on a nonconstant affine
line over $\mathbb F_p$. In particular, the top digit $z_i$ is affine
in $i$ modulo $p$ and has zero third difference. To see nonconstancy, equal digit vectors would
give identical residues modulo $p^4$. Write the cubic coordinates along
this line as $W+iV$. The third finite difference of $F$ is
$6\operatorname{Norm}(V)$, which vanishes under ABBA.
Thus $V=0$. Then $F$ is the top digit plus a constant, so equality of the
two middle values makes that digit constant too. This is impossible.

For a triple, ABAB or AABB, a step nonzero modulo $p^2$ is already detected
by the auxiliary cyclic color. Otherwise $x_0,x_1$ are constant throughout.
The tag on $y$ lifts the matched triple or the two matched pairs. At those
indices the top digits $z_i$ therefore also lie on a line over $\mathbb F_p$:
subtract the low digits from the original congruence and divide by $p^3$.
For a triple use its relation $D$ in this division. Write the matched
$u_i$ as $u_0+ib$. If $b=0$, the step is a nonzero multiple of $p^3$,
and all four $F$-colors are different. For $b\ne0$ use
$\operatorname{Norm}(w+y)=y^3+\operatorname{Tr}(w)y^2+\cdots$.
Completing the cube gives the following expression on the matched indices:

$$
F_i=A(u_0+ib)^3+L(i),\qquad
A=\operatorname{Norm}(e_2)\ne0,\quad \deg L\le1 .
$$

* For three equal $F_i,F_j,F_k$, their second divided difference vanishes.
  Thus $3u_0=-(i+j+k)b$. For three consecutive indices the two outer
  $u$-values have ratio $-1$. At indices $0,1,3$ the three $u$-values
  are $(-4,-1,5)b/3$. At indices $0,2,3$ they are $(-5,1,4)b/3$.
  Each of the latter triples includes two nonzero values with ratio $4$.
* For ABAB or AABB subtract the secant slopes of the two equal pairs.
  They use equal spacings within each pairing. Expanding the cubic gives
  $2u_0=-3b$ in either case. The four $u$-values are
  $(-3,-1,1,3)b/2$. An equal pair therefore has ratio $-3$ or its inverse
  for ABAB, and $3$ or its inverse for AABB.

Every case contradicts the graph coloring. We have constructed a full
cyclic coloring modulo $p^4$ with at most
$8\cdot12^4p\cdot10^k(1+k(M-1)^2)$ colors. Choose
$N^{1/4}\le p\le 2\lceil N^{1/4}\rceil$ by Bertrand's postulate and
restrict. Optimizing $M$ for $Q=p^2$ as above gives the displayed bound
since $\log Q=\tfrac12\log N+O(1)$. The executable implementation checks
every potentially failing progression in the chosen finite cyclic group
and separately checks the cubic calculation for all scalar slopes.
[Construction and verifier](verify_growth.py)

There is also a limitation on polynomial colorings over the field. For
$p>3$, suppose the colors on $\mathbb F_p^n$ are the tuples of values of
$r$ polynomials of degree at most **four**. If $n>4r$, every midpoint
$x$ lies on a nonconstant ABBA progression of the form $x-3v,x-v,x+v,x+3v$.
Indeed, the coefficients of the odd powers of $t$ in $F_j(x+tv)$ are a
linear form $L_j(v)$ and a homogeneous cubic $C_j(v)$. They have a common
nonzero zero by Chevalley–Warning. To see this directly, sum
$\prod_j(1-L_j(v)^{p-1})(1-C_j(v)^{p-1})$ over $v\in\mathbb F_p^n$.
Its degree is at most $4r(p-1)<n(p-1)$, so each monomial sums to zero:
some coordinate has exponent strictly below $p-1$. The number of common
zeros is divisible by $p$ and includes the zero vector, giving another
zero $v\ne0$. Each restriction $F_j(x+tv)$ is then even in $t$.
Shi and Dong's cubic-plus-linear construction attains dimension $4r$ by
taking products. Restricting this construction to lower-dimensional linear
subspaces shows that the minimum number of scalar polynomials of degree
at most four needed to avoid ABBA on $\mathbb F_p^n$ is exactly
$\lceil n/4\rceil$. This counts polynomial coordinates in the palette.

## Finite results near $N=78$

| Result | Headline finding | Verification |
| --- | --- | --- |
| **Proper subsets of $[78]$** | Every proper subset admits seven colors. Every single deletion requires **exactly seven**. | [Lean upper bound](Deletions.lean), [words](colorings.txt), [six-color exclusion](puncture71.cpp), [case enumeration and coverage](puncture78.py) |
| **Arbitrary families of progressions** | Every family of at most 330 of the 975 progressions can be satisfied simultaneously with seven colors. | [Lean theorem](ProgressionFamilies.lean), [integer verifier](verify_progression_families.py), [weighted witness words](progression_families.txt) |
| **Omitting a common difference** | For 24 of the 25 possible differences, omitting that difference permits a seven-coloring of all 78 positions. The remaining case is difference 24. | [Lean theorem](Deletions.lean), [24 witness words](difference_colorings.txt) |
| **Periodic 7-colorings** | Max length with period $\le 40$ is **69**; any valid 7-coloring of $[78]$ has period **$\ge 54$** | [Small-period search](periodic_coloring.cpp), [larger-period search](period_cliques.cpp) |
| **A contiguous cyclically valid 23-block** | The largest seven-colorable interval containing any such block has length **73**. There are 76 extremal words up to reversal and renaming. | [Cyclic census and unrestricted interval extensions](cyclic_block.cpp) |
| **Every single deletion of $[54]$** | The remaining 53 points require **exactly six** colors. The full interval requires seven. | [Lean upper bound](Critical54.lean), [20 words](six_color_punctures.txt), [two lower-bound searches](puncture54.cpp) |
| **Edit distance from near-solutions** | Every valid 7-coloring of $[78]$ differs from Canli's extended 77-word in **$\ge 21$ positions** (and from 281 extended deletion witnesses in **$\ge 15$ positions**), even up to permuting color names | Compiled C++20 branch-and-bound search ([repair.cpp](repair.cpp)) |
| **Color multiplicities on $[78]$** | With any palette, one color occupies at most 17 positions and two occupy at most 31. With seven colors the two largest occupy at most 30. | [Class bounds and completion verifier](class_bounds.cpp) |
| **Reversal up to renaming colors** | The largest even length is 74 and the largest odd length is 71. At 71 there are three colorings up to renaming. | [SAT encoding, witness checks and enumeration](reflection.py) |

---

## 1. Every proper subset of $[78]$ admits seven colors

**Theorem.** *For every proper subset $S \subsetneq [78]$, there is a 7-coloring of $S$ in which every four-term arithmetic progression contained in $S$ uses at least three colors.*

More precisely, for **every** $i\in[78]$ the minimum on
$[78]\setminus\{i\}$ is **exactly seven**. Thus if $h(78)=8$, the interval
is vertex-critical. If $h(78)=7$, each of its seven color classes has at
least two members.

### Proof and certificate

It is enough to check the 78 single-deletion sets $[78] \setminus \{i\}$ ($1 \le i \le 78$). Given any smaller proper subset $S$, pick any element $i \notin S$ and restrict a valid 7-coloring of $[78] \setminus \{i\}$ to $S$; every 4-AP inside $S$ was already valid before restricting.

Rather than storing 78 separate colorings, the certificate in [colorings.txt](colorings.txt) uses just **31 words** of length 78 over the digits `0` through `6`:

1. Read each word both forward and reversed (reversing preserves all 4-APs).
2. In each orientation, check all $\sum_{d=1}^{25} (78 - 3d) = \mathbf{975}$ four-term arithmetic progressions in $[78]$ and collect the failing ones (those with fewer than 3 colors).
3. A word certifies the deletion of position $i$ if and only if **every failing progression contains $i$** — so removing $i$ eliminates every violation simultaneously.

For every one of the 78 positions $i$, [verify_deletions.py](verify_deletions.py) finds a certifying word (the choice of word may depend on $i$).

**Lean 4 formalization:** Lean's kernel independently checks these witnesses and proves the restriction argument in [Deletions.lean](Deletions.lean). The formal theorem `Erdos160.proper_subset_colorable` takes any proper subset of $[78]$ and returns a valid coloring into `Fin 7`.

For the matching lower bound, let $B=[74]\setminus\{25,30,35\}$. A
six-coloring of $B$ would induce one of 17,855 possible equality patterns
on its ten consecutive positions $39,\ldots,48$. Color names are assigned
in order of first appearance. A partial pattern is discarded only when
its already fixed positions force an AP to see at most two colors. Two
independent enumerations give exactly the same list. Fixing each surviving
pattern in turn leaves 61 free positions. When an AP has an equal pair,
its other two colors must differ from each other and from the repeated
color. Propagating these requirements and branching on every remaining
choice excludes all 17,855 cases in 2,505,858,547 nodes.

For $i\le24$ or $i\ge55$, deleting $i$ leaves a consecutive interval of
length 54, which already requires seven colors. For $25\le i\le39$, one
of $B,B+1,\ldots,B+4$ omits $i$, since their omitted positions in the
middle cover $\{25,\ldots,39\}$. Reflection gives the same conclusion for
$40\le i\le54$. This proves the lower bound at every deletion.
[Exhaustive solver](puncture71.cpp), [case enumeration and embedding check](puncture78.py),
[Schluer's exclusion on 54 positions](https://github.com/scottschluer/erdos160/tree/c5745c8e359e4f0602382c18bc512c0e9559207b/results/erdos160-small-values)

### How many progressions could force eight colors?

Every family of **at most 330** four-term progressions in $[78]$ admits a seven-coloring in which each selected progression sees at least three colors. This applies even when the family covers all 78 positions and uses all 25 common differences.

The certificate lists seven-color words with positive integer weights. Include each word and its reversal. Let $T$ be their total weight and let $L$ be the largest, over the 975 progressions, of the weight of words failing that progression. A family of $m$ progressions can rule out words of combined weight at most $mL$. If $mL<T$, at least one word satisfies the whole family. For the 439 certificate rows, $T=33{,}015{,}130$ and $L=100{,}002$. Since $330L=33{,}000{,}660<T$, every 330 progressions admit a common seven-coloring. Any collection that forces eight colors would therefore need at least 331 progressions. The Python verifier computes both integers directly. Lean proves the weighted union bound and uses `native_decide` to audit the concrete words. [Formal theorem](ProgressionFamilies.lean), [witness weights](progression_families.txt), [verifier](verify_progression_families.py)

### Omitting one common difference

On all 78 positions, for each $d$ in $\{1,\ldots,25\}\setminus\{24\}$ there is a seven-coloring whose failing progressions all have difference $d$. The coloring can depend on $d$. The kernel enumerates all 975 progressions for each word. In particular, any family using at most 23 distinct differences can be seven-colored. Thus any family of progressions that forces eight colors must contain a progression of each of those 24 differences. Difference 24 remains unclassified. [Witness words](difference_colorings.txt), [Lean theorem `omit_difference_colorable`](Deletions.lean)

### Extending the deletion witnesses

For each single deletion there is a certified coloring with this further property. **Any valid seven-coloring of the full interval must split at least five of its seven color classes.** A class splits when two positions that had the same color receive different colors in the full coloring.

For each of the 29 words that certifies a single deletion, leave every position whose deletion it certifies unrestricted. Among the remaining positions, the union of any two classes contains three points of a four-term progression. Thus two classes that stay monochromatic must take different colors. Fix the colors of any three classes up to renaming, then search every assignment consistent with those choices. All 1,015 triples are impossible. Reflection gives the result for the reversed words. [Class-extension verifier](class_extensions.cpp)

### Single deletions at the six-color threshold

For each $i\in[54]$, the set $[54]\setminus\{i\}$ needs exactly six
colors. For the upper bound, 20 six-color words and their reversals cover
all deleted positions. Lean verifies the resulting proper-subset theorem
by kernel reduction. For the lower bound, each deletion contains a
translate or reflected translate of $[36]$ or $[52]\setminus\{19,22,25\}$.
Exhaustive searches exclude five colors on those two sets in 165,257 and
723,191 nodes respectively. Together with the existing six-color exclusion
for the full interval, this proves that $[54]$ is vertex-critical.
[Lean upper bound](Critical54.lean), [words](six_color_punctures.txt),
[lower-bound and coverage verifier](puncture54.cpp),
[Schluer's full-interval exclusion](https://github.com/scottschluer/erdos160/tree/c5745c8e359e4f0602382c18bc512c0e9559207b/results/erdos160-small-values)

---

## 2. An exact maximum for periodic colorings

A coloring has **period $p$** if positions $x$ and $x + p$ always receive the same color whenever both belong to the interval — equivalently, the coloring is a prefix of an infinite repeating pattern of length $p$.

**Theorem.** *The longest interval admitting a valid 7-coloring of period at most 40 has length **69**. Furthermore, every valid 7-coloring of $[78]$ must have period **at least 54**.*

### Lower bound ($N = 69$, period $23$)

Repeating the following 23-symbol block three times produces a valid 7-coloring of $[69]$; direct enumeration confirms all $\sum_{d=1}^{22}(69 - 3d) = \mathbf{759}$ four-term progressions use at least three colors:

```text
0 0 1 2 3 0 0 4 1 1 3 5 3 2 6 1 4 2 6 4 5 6 5
```

### Why small and even periods fail immediately

Index the $N$ positions from $0$ to $N - 1$. Two immediate obstructions wipe out small periods and *all* relevant even periods before any computer search begins:

- **Too-short periods ($3p < N$):** The four positions $0, p, 2p, 3p$ all lie inside $\{0, \dots, N-1\}$ and are congruent modulo $p$, so they form a **monochromatic** (1-color) 4-AP. This rules out every $p \le 23$ on $[70]$ and every $p \le 25$ on $[78]$.
- **Even periods ($3p/2 < N$):** The four positions $0, p/2, p, 3p/2$ all fit in $\{0, \dots, N-1\}$. Because $0 \equiv p \pmod p$ and $p/2 \equiv 3p/2 \pmod p$, those four positions repeat an $A, B, A, B$ pattern and use **at most 2 colors**. This eliminates every even period up to $46$ on $[70]$ (and up to $50$ on $[78]$), leaving only odd periods below those cutoffs.

### Why odd periods with $2p \le N$ force every cyclic 4-AP

When $p$ is odd and $2p \le N$, the interval contains at least two full periods, which is long enough to force **every** cyclic 4-AP modulo $p$ (with nonzero step) to appear as the residues of an actual interval 4-AP:

1. Take any cyclic 4-AP modulo $p$ with nonzero step. Reversing it if necessary, represent its step by $d$ with $1 \le d \le (p - 1)/2$, and let its first term be $a \in [0, p - 1]$.
2. If $a + 3d < 2p$, the four positions $a, a + d, a + 2d, a + 3d$ already fit inside $[0, 2p - 1] \subseteq [0, N - 1]$.
3. Otherwise ($a + 3d \ge 2p$), start at $a + 3d - 2p \ge 0$ with step $p - d$. Its four terms are $a + 3d - 2p,\; a + 2d - p,\; a + d,\; a + p$: they visit the exact same residues modulo $p$ in reverse order and finish at $a + p < 2p$.

Because cyclic constraints are symmetric modulo $p$, they make the exhaustive search much faster whenever $2p \le N$. For larger odd periods ($2p > N$), the verifier uses the exact progressions that fit inside the interval.

### Exhaustive search over remaining odd periods

[periodic_coloring.cpp](periodic_coloring.cpp) exhausts every remaining odd period in the table below:

| Length $N$ | Odd periods checked | Constraints used |
| --- | --- | --- |
| 70 or 78, whenever $2p \le N$ | 25, 27, 29, 31, 33, 35, 37, 39 | All cyclic progressions of nonzero step |
| 70 | 37, 39 | Progressions from the actual interval |
| 78 | 41, 43, 45 | Progressions from the actual interval |

*(Here $2p \le 70$ covers $25, \dots, 35$ for $N = 70$, while $2p \le 78$ covers $25, \dots, 39$ for $N = 78$; periods exceeding $N/2$ use exact interval constraints.)*

**How the set-partition search works.** A periodic 7-coloring of period $p$ is a partition of the $p$ residues modulo $p$ into color classes:

- For each progression, let $E$ be its set of **distinct** residues ($|E| = 4$ normally, or $|E| = 3$ when $3 \mid p$ and the step is a multiple of $p/3$, causing the 1st and 4th terms to share a residue).
- To guarantee at least 3 colors on $E$, any single color class must leave **at least 2 elements of $E$ outside it** (otherwise the remaining elements could contribute at most 1 more color). The verifier first generates all color classes satisfying this condition.
- Two disjoint admissible classes can coexist in a valid coloring if and only if their union contains **no** full residue set $E$:
  - For $|E| = 4$, each admissible class holds at most 2 elements of $E$, so two classes fail together precisely when they hold complementary pairs of $E$.
  - For $|E| = 3$, each admissible class holds at most 1 element of $E$ (so two classes can cover at most 2 of its 3 elements). This cleanly handles repeated residues at composite periods.
- The search selects **7 nonempty**, disjoint, pairwise-compatible classes covering all $p$ residues (restricting to exactly 7 nonempty classes is lossless, since splitting a color class into two colors never breaks validity).
- To prune the search, classes are tried in decreasing order of size, pruning whenever the remaining classes are too small to cover the uncovered residues. For cyclic searches, symmetry fixes a largest class up to translation and multiplication by a unit modulo $p$; for interval searches, only reflection of the interval is used.

For length 78, an additional search excludes periods 47, 49, 51, 52, 53 and 57. Periods 48 and 50 fail directly by taking step $p/2$. For each remaining period set $b=\lfloor(p-1)/7\rfloor$. Generate the admissible classes larger than $b$ and join two when they are disjoint and compatible. A partition must select a clique of such classes with total excess over $b$ of at least $p-7b$. For each candidate clique the verifier searches for an exact partition of the remaining residues by compatible classes. For period 47, 38,361 large classes produce just 368 candidate cliques with sufficient excess. None extends. [Larger-period verifier](period_cliques.cpp)

Finally, restricting a periodic coloring of any interval of length $\ge 70$ to its first 70 positions shows no length $> 69$ can have period $\le 40$, establishing **69** as the exact maximum.

### How long can one cyclic block survive?

A block of length 23 is cyclically valid when treating its positions
modulo 23 makes every nonzero-step progression use three or more colors.
There is one seven-color cyclic word up to affine maps of the residues
and color renaming. Its 506 ordered versions up to color renaming are
all considered. Fix such a block at each possible position in an ordinary
interval and allow all outside positions to take any of the seven colors.
At length 73 the search gives 76 distinct whole words up to reversal and
renaming. At length 74 all 13,156 placements up to reflection fail.
Any longer interval containing a block has a length-74 subinterval
containing that block. Thus the maximum possible length is **73**.
[Census, explicit extremal word and extension search](cyclic_block.cpp)

---

## 3. Edit distance from Canli's 77-position coloring

A natural way to hunt for a 7-coloring of $[78]$ is to start from Canli's valid 7-coloring of $[77]$, tack on a 78th color, and then "repair" a small number of positions to remove any bad 4-APs. Our third result proves that **no local repair exists anywhere near Canli's word**.

Using Canli's color labels `0` through `6`, append color `4` at position 78. Out of all 975 four-term progressions in $[78]$, **only a single progression fails**:

$$
(3,\; 28,\; 53,\; 78) \quad\text{with colors}\quad (6,\; 6,\; 6,\; 4).
$$

Notice that *every* choice of color at position 78 fails on this exact same progression, because positions $3, 28, 53$ are already all colored `6`. (Giving position 3 a fresh eighth color fixes $(3, 28, 53, 78)$ without breaking any other progression, giving an immediate direct proof that $h(78) \le 8$.)

**Theorem.** *Every valid 7-coloring of $[78]$ differs from this 78-position extension in **at least 21 positions** (Hamming distance $\ge 21$). The same bound holds after optimizing over all permutations of the seven color names, since relabeling a valid coloring preserves validity.*

Even if the color at position 78 is freely chosen, at least 20 entries of Canli's original 77-position word must change.

Any full seven-coloring also **splits at least six of Canli's seven original color classes**. Indeed, if two original classes stayed monochromatic, they would have different colors, since their union contains three members of a progression. Enumerating all compatible supersets of those two classes, allowing either to acquire points from any other class or position 78, gives 430 cases across the 21 possible choices. An exact five-color completion search excludes each case. [Verifier](class_bounds.cpp)

Allowing the positions to shift gives a separate bound. After any relabeling of the colors, the longest common subsequence of Canli's 77-word and any valid 78-word has length at most **73**. For a common subsequence of length 74, the verifier chooses three omissions in the 77-word and four blanks in the 78-word, places the matched subsequence in order and checks every way to fill the blanks. All 42,836 placements that survive the early checks fail. [Ordered subsequence verifier](subsequence.cpp)

### How the exact radius-20 repair search works

The branch-and-bound verifier ([repair.cpp](repair.cpp)) starts with all 78 positions marked "available for editing" and searches exhaustively for any valid coloring within edit budget $r = 20$:

- **Must-hit sets (hitting-set constraints):** Every currently failing 4-AP forces an edit inside a specific subset of its positions:
  - If a failing progression has **three copies of one color** (a 3+1 failure), at least one of those **three** positions must change (recoloring only the odd position still leaves three identical colors, so at most 2 colors total). If all four positions agree, any three of them suffice for this constraint.
  - If a failing progression is a **two-pair failure** (2+2), at least one of its **four** positions must change.
- **Availability and disjoint-packing pruning:** Intersect each must-hit set with the currently available positions.
  - If any intersection is empty, that failure can no longer be repaired — prune this branch immediately.
  - Pairwise **disjoint** must-hit sets require distinct edits. If more disjoint sets exist than the remaining edit budget, prune; if the count *equals* the remaining budget, then every remaining edit is forced to lie inside their union.
- **Complete branching:** Pick one must-hit set and branch on its *first* position to be changed, in increasing order — locking earlier candidates in that set to their current colors (marking them unavailable) and trying all 6 alternative colors at the selected position.

Because every edit within budget must hit every active constraint at some first index, this explores **every possible repair within budget**, including repairs that temporarily pass through intermediate words with *more* failing progressions. The radius-20 search exhaustively explored **3,296,047,255** nodes and found zero valid 7-colorings.

### Edit distance from the 31 proper-subset witnesses

Applying the same repair verifier to the proper-subset certificates yields a separate bound: start with the 31 length-78 words in [colorings.txt](colorings.txt) and try every possible color at each position whose deletion that word certifies. Identifying words up to permutations of the seven color names leaves **281 distinct words**; none has a valid repair within **14 edits** (every valid 7-coloring of $[78]$ is at distance $\ge 15$ from each of them, and reversing a word preserves this bound).

---

## How often each color can occur

**On $[78]$ the largest possible color class has size 17, and the largest possible union of two color classes has size 31.** These are exact bounds when the palette may be arbitrarily large. There are 44 possible supports of size 17. No size-17 support is compatible with a size-15 support, and no two of the 25,631 size-16 supports are compatible. The verifier exhibits compatible classes of sizes 17 and 14 and gives each remaining position a fresh color. [Class verifier and witnesses](class_bounds.cpp)

With seven colors the two largest classes together occupy **at most 30** positions. To check the stricter bound, fix two entire color classes, use the other five colors on the remaining positions and exhaust all completions. This excludes pairs of sizes $(17,14)$, $(17,13)$ and $(16,15)$. Excluding $(17,12)$ requires another 283,864 pairs up to reflection of the first support. Consequently, if a seven-coloring contains a class of size 17, its second-largest class has size exactly 11. The other six must cover 61 points, so at least one has size 11. The specific 17-set $\{1,2,5,6,15,17,26,27,31,34,58,62,65,67,73,75,78\}$ and its reflection are impossible: none of the 107,583 compatible 11-point classes extends. This leaves at most 42 possible size-17 supports.

## Colorings preserved by reversal up to renaming

Write $c(N+1-i)=\pi(c(i))$ for a permutation of the color names. Applying reversal twice shows that $\pi$ is an involution on the colors used. On seven colors its possible types exchange zero, one, two or three disjoint pairs of names. An odd interval has a center, which must take a fixed color.

**The largest odd length admitting such a seven-coloring is 71.** At 73, all four permutation types are impossible. Removing matching endpoints preserves the symmetry, so this excludes every longer odd interval. At 71 the four types give respectively 0, 0, 2 and 1 colorings up to color permutation. All seven names occur because the interval contains $[54]$. Consequently the reversal permutation of each witness is unique.

In all three extremal words, **positions 18, 36 and 54 have the same color**. Appending position 72 therefore makes $(18,36,54,72)$ use at most two colors, and prepending position 0 does the same to $(0,18,36,54)$. None of the three words can extend even one position in either direction, even if that position receives a fresh color.

**The largest even length admitting this symmetry is 74.** The following length-74 word has reversal permutation $(0\;1)(2\;3)$, fixing the three other colors.

```text
20452363102656041316330552642544021201303144534635512260204165631026235413
```

At length 76, zero or one transposed pair is excluded by the arbitrary-palette bound below. CaDiCaL exhaustively excludes both the two-pair and three-pair cases at 76. Removing equally many positions from each end preserves the symmetry, so this excludes all greater even lengths. Both cases were also separately excluded at 78. Together with the odd maximum of 71, this makes **74 the longest interval of either parity** whose seven-coloring is preserved by reversal up to renaming.

The separate maxima for each involution on a palette of seven are as follows. Unused colors are allowed.

| Number of transposed pairs | Largest odd length | Largest even length |
| --- | --- | --- |
| 0 | 5 | 2 |
| 1 | 57 | 44 |
| 2 | 71 | 74 |
| 3 | 71 | 74 |

For zero pairs a centered progression in a symmetric word has the pattern $A,B,B,A$. Such a progression exists from even length 4 and from odd length 7. The words `00` and `01210` realize lengths 2 and 5. For one pair the seven-color SAT checks give witnesses at 44 and 57 and exclude 46 and 59. Both the two- and three-pair cases have witnesses at 71 and 74.

The verifier chooses the colors of one half and reads the other half using $\pi$. A four-tuple has at least three colors exactly when at most one of its six pairs has equal colors. The CNF imposes this condition on every progression. Names of fixed colors and names of transposed pairs are ordered by first use from the center outward. The first occurrence of a transposed pair also fixes its orientation. For the census, a blocking clause removes each verified half-word before the next solve. [Reflection verifier](reflection.py)

With an arbitrary palette and **at most one transposed pair**, the sharp maximum is 44 for even intervals and 65 for odd intervals. To see why this is a finite three-state problem, give each reflected pair that uses a fixed color its own fresh fixed color. Splitting these labels preserves validity. A half-position now has three choices, namely its private fixed label or one of the two exchanged labels. The checker finds witnesses at 44 and 65 and excludes 46 and 67 by exhaustive search. [Three-state verifier](one_transposition.py)

## Reproduce

The Lake target checks the logarithmic limit theorem against mathlib
v4.36.0 and verifies the finite coloring certificates. On a fresh checkout, run the following from this directory:

```sh
lake exe cache get
lake build
```

Run the commands below from this directory to replay the explicit colorings
and finite searches with Python 3 and a C++20 compiler.

```sh
python3 verify_deletions.py
python3 verify_progression_families.py
python3 verify_growth.py
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic symmetric_bases.cpp -o /tmp/erdos160-symmetric
/tmp/erdos160-symmetric
c++ -O3 -std=c++20 -Wall -Wextra -Werror cyclic_block.cpp -o /tmp/erdos160-cyclic-block
/tmp/erdos160-cyclic-block
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic puncture54.cpp -o /tmp/erdos160-puncture54
/tmp/erdos160-puncture54 six_color_punctures.txt
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic puncture71.cpp -o /tmp/erdos160-puncture71
checkpoint_dir=$(mktemp -d)
python3 puncture78.py --solver /tmp/erdos160-puncture71 --jobs 3 --checkpoint "$checkpoint_dir"
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic class_extensions.cpp -o /tmp/erdos160-classes
/tmp/erdos160-classes colorings.txt
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic class_bounds.cpp -o /tmp/erdos160-class-bounds
/tmp/erdos160-class-bounds
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic subsequence.cpp -o /tmp/erdos160-subsequence
/tmp/erdos160-subsequence 3
python3 one_transposition.py
for t in 0 1 2 3; do python3 reflection.py 71 "$t" --all; python3 reflection.py 73 "$t"; done
for n in 44 46 57 59; do python3 reflection.py "$n" 1; done
for t in 2 3; do python3 reflection.py 74 "$t"; done
for t in 2 3; do python3 reflection.py 76 "$t"; python3 reflection.py 78 "$t"; done
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic periodic_coloring.cpp -o /tmp/erdos160-periods
/tmp/erdos160-periods
c++ -O3 -march=native -std=c++20 period_cliques.cpp -o /tmp/erdos160-period-cliques
for p in 47 49 51 52 53 57; do /tmp/erdos160-period-cliques "$p"; done
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic repair.cpp -o /tmp/erdos160-repair
/tmp/erdos160-repair 20
python3 verify_deletions.py --check-repairs /tmp/erdos160-repair --radius 14
```

### Trust boundaries and notes

- The proper-subset theorem (`Erdos160.proper_subset_colorable`) is verified inside Lean 4's kernel ([Deletions.lean](Deletions.lean)) and cross-checked in Python ([verify_deletions.py](verify_deletions.py)).
- The six-color exclusion for single deletions from $[78]$ uses the compiled puncture solver. A fresh checkpoint directory runs every solver case. Reuse the directory to resume an interrupted run.
- The class-extension exclusions, periodic exclusions and edit-distance lower bounds rely on compiled C++20 exhaustive checks running outside Lean. The periodic verifier also checks the length-69 positive witness; to test a single period and length directly (for example, period 41 on $[78]$), run `/tmp/erdos160-periods 41 78`.
- The reflection census at lengths 71 and 73 was also replayed using CaDiCaL 2.1.2 with internal checking. The script accepts an external binary through `--solver` and can export the CNF through `--dimacs`. The arbitrary-palette one-transposition proof uses a separate Python constraint search.
- **Open status:** The unrestricted search has produced neither a 7-color witness on $[78]$ nor an exclusion of all such witnesses.

## References

- [Erdős Problem #160](https://www.erdosproblems.com/160)
- [Scott Schluer — six-color exclusion](https://github.com/scottschluer/erdos160/tree/c5745c8e359e4f0602382c18bc512c0e9559207b/results/erdos160-small-values) on $[54]$
- [Arhan Canli — seven-coloring witness](https://github.com/arhancanli/quantavane-erdos-results/blob/6a4c61d4b873f9cccc66c903993d319d3d2c1250/160/witness/k7_N77.txt) on $[77]$
