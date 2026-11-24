# Two prescribed values on the Pell conic

Let $x,y,z$ be rational polynomials on $u^2-3v^2=1$ of total degrees at most $4,3,6$, respectively. Prescribe $(x,y,z)=(0,1,1)$ at $(u,v)=(1,0)$. **Neither $(1,0,-1)$ nor $(-2,3,1)$ is possible at $(2,1)$** for an identity $z^2+y^2z+x^3=2$. Both exclusions already hold over $\mathbb Q_2$.

## Why the finite tests cover arbitrary denominators

Put $w=u-1-v$. It vanishes at both marked points, with $v=0$ at the first and $v=1$ at the second. Since

$$v^2=(1+w)v+w+w^2/2,$$

each coordinate has the form $P(w)+vQ(w)$, with $\deg P\le d$ and $\deg Q<d$ for its respective bound $d$. The marks fix the two constants $P(0),Q(0)$ as integers.

For every nonzero coefficient $a_i$ with $i>0$ in any of the six polynomials, consider $-v_2(a_i)/i$. Let $h$ be their maximum. If all six polynomials have only constant terms, use the integral case below.

* **$h\le1/2$.** The coefficient $2^{\lfloor i/2\rfloor}a_i$ is integral at 2. The identity $w^2/2=v^2-v-(1+v)w$ therefore expresses every monomial $a_iw^i$ in the original integral Pell-coordinate ring, preserving its degree bound. In this ring one can write each coordinate $f(v)+wq(v)$. For prescribed values $a,b$ at the two marks, $f=a+(b-a)v+v(v-1)r(v)$. Coefficient comparison gives a contradiction modulo 4 at the first target and modulo 4096 at the second. The latter admits an explicit model modulo 2048. [Marked polynomial normal form](TwoPointMarkedPolynomial.lean) · [Lean modulo-4096 proof and modulo-2048 witness](two_point_alternate_two.lean)
* **$h>1/2$.** Write $h=k+j/e$ in reduced terms, allowing $j=0,e=1$. An index attaining the maximum satisfies $e\mid i$, so $e\le6$. Use the basis $E_i=w^i/2^{\lfloor hi\rfloor}$. All coordinate coefficients in this basis are integral at 2, and at least one positive-index coefficient with $e\mid i$ is odd. The multiplication rule is
  $$E_a E_b=2^{\lfloor h(a+b)\rfloor-\lfloor ha\rfloor-\lfloor hb\rfloor}E_{a+b}.$$
  Its exponent depends only on $j/e$. In the rule for $v^2$, multiplication by $w$ and by $w^2/2$ brings additional powers of two. For $k\ge1$, write $2^k=2H$ and $2^{2k-1}=2H^2$. Letting $H$ be an arbitrary residue covers all such integer parts in a single test for each fraction. The remaining cases have $k=0$ and $j/e>1/2$. All products are integral in the normalized basis.

There are twelve reduced fractions in $[0,1)$ with denominator at most six. All twelve occur with $k\ge1$, and five also require the separate $k=0$ test. For each prescribed target, Lean checks that every one of these 17 systems is inconsistent modulo 8. It also checks that the list covers every admissible fraction. The theorem takes all 23 unknown coordinate coefficients and $H$ as arguments. The input conditions are the cubic identity and an odd coefficient at an active index. A separate implementation using Z3 reproduces every result. The step from rational 2-adic valuations to these normalized finite systems is the mathematical argument above. [Lean verification of all fractions](TwoPointBalanced.lean) · [Independent bit-vector checker](two_point_two_adic.py)

There is a stronger restriction at the first target. If all three values at $(2,1)$ are integral at 2, then $x(2,1)$ must be even. The equation permits just four odd-$x$ triples modulo 4. An independent enumeration of their correction matrices matches 26 inconsistent subsystems verified by Lean. This broader result uses Python for the exhaustive matching. For the alternate target the same proof excludes any integral triple congruent to $(-2,3,1)$ modulo 4096, since all the tests only use the marked values modulo a divisor of 4096. [Odd second abscissas](TwoPointPrimaryTwo.md) · [Alternate denominator analysis](TwoPointAlternateTwo.md)

## Exact equations and the recurrence

In the rational chart $t=v/(u+1)$, put $L=1-3t^2$ and write $x=X/L^4,\ y=Y/L^3,\ z=Z/L^6$. The numerator degrees are at most $8,6,12$. Sending the marks $0,1/3$ to $0,\infty$ by $t=s/(1+3s)$ gives the denominator $D=1+6s+6s^2$. For the transformed numerators, $W=2Z+Y^2$ satisfies

$$W^2=Y^4+8D^{12}-4X^3.$$

The marks fix the constant and top coefficients of $X,Y,W$. In particular $W_0=3$ and $W_{12}=6^6(2z_1+y_1^2)$, both nonzero for the two targets. Coefficients $1,\ldots,6$ of this identity recover $W_1,\ldots,W_6$ successively by division by $2W_0$. Coefficients $23,\ldots,19$ recover $W_{11},\ldots,W_7$ by division by $2W_{12}$. The twelve middle coefficients give twelve equations in the seven free coefficients of $X$ and five of $Y$. The elimination is exact over $\mathbb Q$. One recovers $Z$ from $(W-Y^2)/2$. [Elimination and equation exporter](two_point_elimination.py)

For any future chart with an integral seed and a changed $x$-value at $t=1/3$, Lean proves that a rational polynomial identity of these degrees implies infinitely many integer solutions. The recurrence $(u,v)\mapsto(2u+3v,u+2v)$ returns to the seed modulo any common coefficient denominator along an infinite subsequence. The proof also establishes that the resulting triples take infinitely many values. [Lean amplification theorem](MixedPellAmplification.lean)

## Residue calculations at 7 and 13

Both marks also control denominators at 13. In the $t$ chart the marks $c=0$ and $c=1/3$ reduce to distinct elements of $\mathbb F_{13}$, and $L(c)$ is a unit at each. Suppose a coefficient of $X,Y,Z$ has negative valuation. Integral translation preserves this property, so at either center there is a positive maximum of $-v_{13}(a_i)/i$ among the Taylor coefficients of positive index. Write that maximum as $h$ and rescale $t=c+\lambda T$ with $v_{13}(\lambda)=h$ in a totally ramified extension. Reduction gives an ordinary polynomial solution over $\mathbb F_{13}$, since $L$ reduces to the nonzero constant $L(c)$. Some coordinate is nonconstant. The existing exhaustive ordinary-polynomial calculation shows that its $x$-coordinate has degree at least six. [Ordinary-polynomial calculation](OrdinaryPolynomial.md)

Consequently some Taylor coefficient $a_k$ of $X$ at each center has $k\ge6$ and $v_{13}(a_k)=-kh$. Every nonzero coefficient at a lower index $i$ has $v_{13}(a_i)\ge-ih>-kh$. Multiply $X$ by a power of 13 so that its minimum coefficient valuation is zero. Translation by either center preserves that minimum because the translation and its inverse are integral. The resulting nonzero residue polynomial would vanish to order at least six at each of two distinct points despite having degree at most eight. This is impossible. Thus the full modular census at 13 covers rational coefficients of arbitrary height. [Lean multiplicity and slope lemmas](TwoPointDegree.lean)

The finite census fixes both $x$-values, leaving seven free numerator coefficients. For each of the $p^7$ candidates it factors $2L^{12}-X^3$, tests degree-12 divisors normalized by $Z(0)=1$, and checks whether the complementary divisor minus $Z$ is a square with the prescribed $y$-values. At $p=7,13$ the leading coefficient of $2L^{12}-X^3$ is nonzero because 2 is a noncube. The constant and marked values in these two searches are nonzero as well. Candidates that lose poles upon reduction are included. [Divisor census](two_point_census.py) · [Lifting and line-intersection checks](two_point_lifts.py)

The numbers of distinct residue triples for the first and second targets were respectively 2 and 1 modulo 7, and 4 and 4 modulo 13. Every listed residue lifts through $p^{50}$. The obstruction at 2 explains why pursuing any one of these local lifts cannot produce a rational substitution for either marked pair. [Enumeration output](two_point_residues.jsonl)

As a further check, $(8,7,-15)$ satisfies the original surface equation and the corresponding quartic system has a model modulo 4096. However, enumerating the $5^7=78{,}125$ possible $X$ numerators gives no model over $\mathbb F_5$ at these marks. A rational chart through this new target would therefore have to have some coefficient with a denominator divisible by 5 in the $t$ chart. [Lean modulo-4096 witness](two_point_alternate_two.lean) · [Modulo-5 enumerator](two_point_census.py)

To repeat the checks, run

~~~sh
lake -d .. build
uv run --with z3-solver==4.15.4.0 python two_point_two_adic.py
uv run --with python-flint==0.9.0 python two_point_primary_two.py
uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
uv run --with python-flint==0.9.0 python two_point_elimination.py --target 1
uv run --with python-flint==0.9.0 python two_point_census.py --prime 5 --endpoint 8 7 -15
uv run --with python-flint==0.9.0 python two_point_lifts.py two_point_residues.jsonl --precision 50
~~~
