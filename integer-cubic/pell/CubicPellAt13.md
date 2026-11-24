# Cubic Pell substitutions at 13

For every nonsquare rational $D$, a nonconstant polynomial substitution on $u^2-Dv^2=1$ through $(0,1,1)$ must have $x$ of pole order at least four at each of the two points at infinity. The proof checks both possibilities for the smaller cubic factor of $2-x^3$. [Argument for the marked point](#marked-seed)

Suppose three rational functions on a pointed Pell conic satisfy
$x^3+y^2z+z^2=2$ and take integer values at the marked rational point.
Suppose each coordinate has poles only at the two ends and has pole order at
most three at each end. These assumptions include maps polynomial of total
degree at most three in the coordinates of $u^2-Dv^2=1$.

* If $v_{13}(D)$ is odd, the map is constant.
* If $D$ is a square in $\mathbb Q_{13}$ and the map is nonconstant, its
  reduction in the split Laurent coordinate is integral and nonconstant.

The first conclusion holds for every integral seed and every rational
$D\ne0$ of the indicated square class. Both statements use the following
finite-field calculation. The valuation arguments below are written proofs.

## Ordinary polynomial solutions modulo 13

Every solution in $\mathbb F_{13}[t]$ for which **all three** coordinates
have degree at most six is constant. The case $\deg x\le5$ also holds for
unrestricted $y,z$. [Degree-five proof and finite checks](OrdinaryPolynomial.md)

For $\deg x=6$, put $z'=z+y^2$. The polynomial $zz'=2-x^3$ has degree 18.
Since $\deg z'\le12$ and $\deg z\le6$, the degrees must be 12 and 6
respectively. Translate $t$ to remove the degree-five coefficient of $x$.
Scaling $t$ by a unit and multiplying $x$ by a cube root of unity yields
two representatives for its leading coefficient, 1 and 2. The five lower
coefficients are free. For each of the resulting $2\cdot13^5=742586$
polynomials, factor $2-x^3$, enumerate all monic degree-six divisors and
test their scalar multiples for $(2-x^3)/z-z$ to be a square. There are
737856 monic divisors in total and no solutions. The checker also tests the
degree-five case by fixing the smaller cubic factor and varying $x$ modulo
that factor. [Exact checker](cubic_ordinary_at13.py)

## Integral Laurent coefficients

Take $K=\mathbb Q_{13}$ if $D$ is a local square, or
$K=\mathbb Q_{13}(\sqrt D)$ if $v_{13}(D)$ is odd. In both cases the residue
field is $\mathbb F_{13}$. The Laurent coordinate $q=u+\sqrt D\,v$ identifies
the two poles with zero and infinity. Multiplication by the inverse of the
marked point gives a coordinate with $q=1$ at that point. Write each function
as $f(q)=\sum_{i=-3}^3 a_i q^i$.

Write $f(1+t)=A_f(t)/(1+t)^3$. The three polynomials $A_f$ have degree at
most six and integral constant coefficients. If any coefficient has negative
valuation, let $h>0$ be the greatest value of $-v([t^i]A_f)/i$ over their
nonzero coefficients of positive degree. In a totally ramified extension
take $v(\lambda)=h$. Substitution of $t=\lambda T$ makes all numerators integral,
preserves some nonconstant coefficient as a unit and reduces the denominator
to 1. This produces a forbidden nonconstant ordinary polynomial solution
with all degrees at most six. Hence all $A_f$ are integral, as are the Laurent
coefficients, by translating back from $t=q-1$.

In either case, if the three reductions in $q$ were constant, all coefficients
$a_i$ with $i\ne0$ would have positive valuation. For a nonconstant map
we can exchange $q$ and $q^{-1}$ so that some positive-index coefficient is
nonzero. Take the least $r=v(a_i)/i$ over all such coefficients in the three
functions. It is positive. In a totally ramified extension put
$q=\mu^{-1}T$ with $v(\mu)=r$. Negative powers disappear in the reduction,
and a positive power survives. This yields a nonconstant ordinary solution
of degree at most three. Thus a nonconstant map must have nonconstant
Laurent reduction.

## Ramified quadratic case

The nontrivial automorphism $\sigma$ of $K/\mathbb Q_{13}$ exchanges $q$ and
$q^{-1}$, also after translation by the marked point. Hence
$a_{-i}=\sigma(a_i)$. The residue action is trivial because the extension is
totally ramified. The reductions of the three functions are therefore
polynomials of degree at most three in $s=q+q^{-1}$: each
$q^i+q^{-i}$ is a monic polynomial of degree $i$ in $s$ for $i>0$. Since $s$ is
transcendental, these polynomials satisfy the original equation identically.
The finite-field calculation forces them to be constant. The preceding
rescaling then forces the original map to be constant.

## Quadratic x and a cubic factor

A related obstruction has a separate end-to-end Lean certificate. Write
$\alpha^3=2$. A cubic factor $z(s)$ of $2-x(s)^3$ for a quadratic $x(s)$
is irreducible over $\mathbb Q$, since a rational root would give a rational
cube root of 2. A root $\theta$ generates $\mathbb Q(\alpha)$ with
$x(\theta)=\alpha$. Translate the variable so that
$\theta=a\alpha+b\alpha^2$, and put $d=a^3-2b^3$. Its monic minimal
polynomial is $P=s^3-6abs-2a^3-4b^3$. The quadratic
$G=a^2s-bs^2+4ab^2$ satisfies $G(\theta)=d\alpha$, so $x=G/d$.
Writing $z=uP$ and $Q=(2d^3-G^3)/P$, the remaining equation is
$$u d^3 y^2=Q-d^3u^2P.$$
Lean proves that for all rational $a,b$ not both zero and every $u\ne0$,
the cubic on the right has nonzero discriminant. When its cubic term
cancels, Lean rules out an integral point via the tangent relation to
$V^2=U^3-2$. Thus neither a repeated-root reduction nor leading-term
cancellation in this pencil yields an integral Pell family. The Lean proof
combines the two complementary scalars $u$ and $b^3/(d^3u)$, then proves
a projective obstruction modulo 13 and descends on their common denominator.
[Lean identities and obstruction](QuarticFactorPencil.lean)

Reproduce the finite-field computation with
`uv run --with python-flint==0.9.0 cubic_ordinary_at13.py`.

<a id="marked-seed"></a>

## All Pell discriminants through the seed $(0,1,1)$

Let $D$ be any nonsquare rational number and consider a map from a pointed Pell
conic of discriminant $D$, regular away from its two ends, taking the value
$(0,1,1)$ at the marked rational point. **If $x$ has pole order at most three
at each end, the entire map is constant.** This is a computer-assisted
arithmetic argument. Lean checks the algebraic obstructions, with the enumerations
and local changes of coordinates verified separately as described below.

Orders at most two are covered by the earlier pole-order argument. At order
three, $y$ has order three and the two factors $z$ and $z+y^2$ have orders
three and six in some order. The surface involution $z\mapsto-z-y^2$ lets
us take $z$ to have order three. The marked value in this orientation is
either $(0,1,1)$ or $(0,1,-2)$. [Smaller pole orders](pole_two.md) ·
[Formal pole constraints](PoleOne.lean)

Odd $v_{13}(D)$ is covered above. For even valuation choose $d=3$ if $D$
is a square in $\mathbb Q_{13}$ and $d=2$ otherwise. These represent the
two unit square classes. By a local change of variable and translation of
the marked point, we can write the conic as $u^2-dv^2=1$ with the mark at
$(1,0)$. With $L=1-dt^2$ the three coordinates have common denominator $L^3$
and numerator degrees at most six. The numerators have integral coefficients:
otherwise the first balancing argument applied in the rational $t$ chart
produces a nonconstant ordinary solution of degrees at most six over
$\mathbb F_{13}$, since the balanced denominator reduces to 1.

For the unramified nonsplit case, we must also exclude constant reduction.
Over the unramified quadratic splitting field use
$q=(1+\sqrt d\,t)/(1-\sqrt d\,t)$. The change from $t$ numerators over $L^3$
to Laurent coefficients in $q$ is integral in both directions because
$2\sqrt d$ is a unit. If the reduction were constant, dilating $q$ as above
would yield a nonconstant ordinary polynomial solution of degree at most
three in each coordinate over $\mathbb F_{169}$. Its value at zero equals
the marked seed modulo 13, since the nonconstant Laurent coefficients all
had positive valuation. For each of the two seeds, the checker rules this
out by normalizing the first nonzero coefficient of $x$ and factoring
$2-x^3$. The numbers of candidate $x$ for first exponents 1, 2 and 3 are
28561, 338 and 1. Constant $x$ at either seed is zero, so $z(z+y^2)=2$
forces the other two coordinates to be constant as well.

It remains to examine nonconstant reductions of
$X^3+ZY^2+Z^2L^3=2L^9$ over $\mathbb F_{13}$. Multiplying $X$ by a cube
root of unity and replacing $t$ by $-t$ preserves either seed. For each $d$,
there are 804835 lexicographically normalized candidate numerators $X$.
For each we factor $2L^9-X^3$, take all degree-at-most-six divisors $Z$
with the required constant coefficient, and test whether the resulting $Y^2$
is a polynomial square of degree at most twelve. Each row also has one
constant orbit, already excluded.

| $d$ | Marked $z$ | Nonconstant orbits | Orbits excluded at a simple root of $L$ | Orbits excluded modulo $13^2$ |
| --- | --- | --- | --- | --- |
| 2 | 1 | 1 | 1 | 0 |
| 2 | −2 | 1 | 1 | 0 |
| 3 | 1 | 2 | 2 | 0 |
| 3 | −2 | 3 | 2 | 1 |

In the simple-root column there is a root of $L$ where $X$ vanishes to
order one, $Y$ vanishes to order at least two, and $Z$ is a unit. A local
rescaling at the lifted root rules out keeping the order-three pole of $x$.
This applies in either residue field. The change of coordinates over the
local field preserves the two geometric ends, and a rational $x$ of order
three over the original nonsplit conic has that order at both ends. In the
last column a left-kernel vector of the 18 first-correction equations pairs
to 4 with the correction target in $\mathbb F_{13}$. This calculation uses
the exact marked value $z=-2$. Negation of $t$ and multiplication of $X$
by the cube roots of unity both lift to the local field and preserve that
exact value. [Local proof](CubicSimplePole.md) · [First-correction Lean certificate](CubicSeed13Lift.lean) · [Exhaustive field checks](cubic_seed13.py)

Reproduce the seed computations with
`uv run --with python-flint==0.9.0 cubic_seed13.py`.
