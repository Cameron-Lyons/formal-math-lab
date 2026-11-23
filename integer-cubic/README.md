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

## Verification

Run `lake build` and `lake exe boundedSearch`. `IntegerCubic.lean` contains the kernel-checked family, injectivity, and denominator proofs. The degree bound uses the executable `BoundedSearch.lean` together with the written reduction above.
