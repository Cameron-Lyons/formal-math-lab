# Integer points and tangent planes

Three solutions have distinct first coordinates of absolute value greater
than 30,000,000. Lean checks each equation and inequality directly. [Lean witnesses](WitnessSearch.lean)

| $x$ | $y$ | $z$ |
| ---: | ---: | ---: |
| −280,813,200 | 157,750,309 | 889,840,366 |
| −71,709,552 | 18,357,983 | 1,094,157,121 |
| 36,307,388 | 16,351,199 | −179,013,631 |

## Search by cube roots

Put $d=|z|$. Every solution satisfies $x^3\equiv2\pmod d$.
For each root $0\le r<d$ write $x=r+qd$. The square to test is
$$
y^2=\left|\frac{r^3-2}{d}+d+3r^2q+3rdq^2+d^2q^3\right|.
$$
The expression inside the absolute value is $(x^3-2)/d+d$.
A positive value gives $z=-d$ and a negative value gives $z=d$.
The code builds the roots modulo prime powers by Hensel lifting at primes
greater than three, and combines them using the Chinese remainder theorem.
There is no root modulo 4 or 9. The table records three runs. The prime bound
limits the largest prime divisor of $d$. The $d$ bounds are inclusive, the
quotient satisfies $|q|\le Q$, and the $|x|$ lower bound is strict.
[Search program](witness_search.cpp)

| Min $d$ | Max $d$ | Prime bound | $Q$ | Min $\lvert x\rvert$ | Root classes | Square tests |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 60,000,000 | 400,000 | 14 | 5,547,568 | 18,597,267 | 513,888,097 |
| 60,000,001 | 220,000,000 | 1,000,000 | 18 | 8,593,390 | 47,778,072 | 1,761,036,829 |
| 60,000,001 | 1,400,000,000 | 50,000 | 4 | 8,593,390 | 187,609,579 | 1,679,989,814 |

```sh
g++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror witness_search.cpp -o /tmp/witness_search
/tmp/witness_search 60000000 400000 14 1 5547568
/tmp/witness_search 220000000 1000000 18 60000001 8593390
/tmp/witness_search 1400000000 50000 4 60000001 8593390
```

## Tangent planes at infinity

Homogenize the cubic as $X^3+Y^2Z+Z^2T=2T^3$. At the rational point at
infinity $[-a^2b:a^3:b^3:0]$ with coprime $a,b$, an affine point on the
tangent plane satisfies
$$3a^4b^2x+2a^3b^3y+a^6z+b^6=0.$$
Thus $a$ divides $b^6$ and $a=\pm1$. After scaling the parameters, put
$a=1$ and $b=n$. The plane becomes $z+3n^2x+2n^3y=-n^6$. Set
$m=-(3x+2ny+n^4)$ and $A=x+m$. Then $z=n^2m$, $x=A-m$, and
$2ny=2m-3A-n^4$. Writing $H=n^8+6n^4A-3A^2$, substitution and a Bézout
identity give
$$mH=4(2-A^3),\qquad H\mid 4(n^{24}+540n^{12}-108),\qquad
3(A-n^4)^2=4n^8-H.$$
For $n\ge1$ the integer on the right of the divisibility is positive.
Enumerate its signed divisors and test the square condition to recover all
integer points on each such plane. For $1\le n\le250$ the check with proven
factorization yields just $(0,-1,1)$ on the plane $n=1$.
Negating $n$ negates $y$. At $n=0$ the plane $z=0$ requires $x^3=2$.
[Lean reduction](WitnessTangent.lean) · [PARI/GP finite check](witness_tangent.gp)

## Fixed small ordinates

For even $y$, $(X,Y)=(-x,z+y^2/2)$ satisfies $Y^2=X^3+y^4/4+2$.
For odd $y$, $(X,Y)=(-4x,4(2z+y^2))$ satisfies
$Y^2=X^3+16(y^4+8)$. For all $|y|\le27$ these constants lie within
the Bennett–Ghadermarzi complete Mordell tables. Filtering their points by
the displayed substitutions gives $x\in\{-32,-7,-2,0,1,8,20,26\}$. The
same test on the even fibers $|y|\le78$ gives a largest $|x|$ of 1,759,
attained at $|y|=32$. This finite-fiber classification uses the published
tables. [Bennett–Ghadermarzi data](https://personal.math.ubc.ca/~bennett/BeGa-data.html)
