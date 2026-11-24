# Does $z^2+y^2z+x^3=2$ have infinitely many integer solutions?

The question remains open. The degree bound below rules out the polynomial pattern that worked for two related equations. [Grechuk, Table 6](https://arxiv.org/html/2404.08518v11#S5) · [Epoch's two families](https://epoch.ai/files/open-problems/small-diophantine-two-families.pdf)

## A polynomial family would need degree at least six in $x$

Suppose $x,y,z\in\mathbb Q[T]$ give a nonconstant solution and take integer values together at some rational $T$.

**First work modulo 13.** The equation factors as
$$
z(z+y^2)=2-x^3.
$$
For a fixed $x$, put $f=2-x^3$. Try each polynomial divisor $d$ of $f$, including scalar multiples. It gives a solution exactly when $f/d-d$ is a square, since we can then take $z=d$ and $y^2=f/d-d$.

The Lean executable finds **zero** successes for nonconstant $x$ of degree at most five. It checks 37,883 choices of $x$ after changes of parameter $T\mapsto aT+b$. Translation removes the next-to-leading coefficient, and scaling identifies equivalent leading coefficients. If $x$ is constant, $2-x^3$ is a nonzero constant because 2 is not a cube modulo 13. Its two factors must then be constant, forcing $y,z$ to be constant too.

**Now pass from rational coefficients to the finite field.** Translate the integral point to $T=0$. For each nonzero coefficient $c_i$ of positive degree $i$ in any of $x,y,z$, write $c_i=13^v u_i$ with numerator and denominator of $u_i$ prime to 13. Let $r$ be the smallest ratio $v/i$. Keep $u_i\bmod13$ when $v=ri$, discard terms with $v>ri$, and reduce constants normally.

At least one nonconstant term survives. The equation survives too. In degree $j$, every product of coefficients has exponent of 13 at least $rj$, with equality only for products of retained terms. If any survive, divide the coefficient identity by $13^{rj}$ and reduce modulo 13. This produces a nonconstant solution over $\mathbb F_{13}$ without increasing $\deg x$. The finite check therefore forces $\deg x\ge6$.

## An infinite family with $x,z$ integers

Put $y=9k-5/13$ and $z=-78k^2+12k-2$. Expanding gives
$$
2-z(z+y^2)=\frac{18(k+2)}{169}(13k-2)^3.
$$
Choose $k=2028n^3-2$ for $n=0,1,2,\ldots$. The first factor becomes $(6n)^3$, so $x=6n(13k-2)$ gives a solution. The $y$-coordinates strictly increase and each has reduced denominator 13.

## Pell substitutions and integer witnesses

On $u^2-3v^2=1$, put $L=1-3t^2$. Consider a rational polynomial identity

$$
A^3+B^2J+J^2=2L^{12},\qquad (x,y,z)=(A/L^4,B/L^3,J/L^6).
$$

Assume $\deg A\le8,\ \deg B\le6,\ \deg J\le12$. Lean proves that if $x$ is nonconstant and the triple at $t=0$ is integral, the Pell recurrence gives infinitely many integer solutions. The rational identity with those properties remains to be found. At the seed $(0,1,1)$, exact modular searches ruled out more than 21 million candidate first coordinates in each of two bases, within the specified reduction classes and height bound 171. [Lean recurrence and theorem](pell/MixedPellAmplification.lean) · [Search bounds, counts and commands](pell/QuarticFreeMark.md)

Lean also rules out the quintic substitution $az=2-r^3,\ x=r-p^2z$ for every nonzero rational $a$ on a nonsplit Pell conic, when $r,p$ have simple poles at the two conjugate ends and all coordinates are regular away from them. This exclusion holds at every coefficient height. [Lean proof](pell/QuinticSquareObstruction.lean) · [Quintic substitutions and searches](pell/QuinticFactorSearch.md)

Three explicit integer triples have distinct first coordinates with $|x|>30{,}000{,}000$. Lean checks each triple and inequality directly. Epoch's intermediate challenge asks for three distinct first coordinates with $|x|>10^{50}$, which remains open here. [Witnesses](pell/WitnessSearch.md) · [Lean proof](pell/WitnessSearch.lean) · [Epoch challenge](https://epoch.ai/frontiermath/open-problems/small-diophantine)

## Verification

Run `lake build` and `lake exe boundedSearch`. `IntegerCubic.lean` contains the kernel-checked family, injectivity, and denominator proofs. The degree bound uses the executable `BoundedSearch.lean` together with the written reduction above.

From this directory, `lake build SmallCubic` checks the Pell library on its own. The main declarations are `SmallCubic.MixedPell.infinite_of_nonconstant_quartic_chart`, `SmallCubic.QuinticSquareObstruction.no_negative_square_lift` and `SmallCubic.WitnessSearch.three_large_solutions`.

Run the search commands in the linked notes from the [pell directory](pell/). Most use Python with `python-flint==0.9.0` via `uv`. Individual notes specify when a C++17 compiler, PARI/GP or Z3 is needed.
