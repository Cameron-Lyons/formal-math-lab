# Integer points and tangent planes

Alongside searching for infinite polynomial or Pell families on the cubic surface $z^2 + y^2 z + x^3 = 2$, it is natural to look directly for large explicit integer points and to classify integer points on special geometric slices of the surface. This note collects three results:

1. **Three Lean-verified large integer witnesses** with distinct $x$-coordinates and $|x| > 30{,}000{,}000$, found via a C++23 cube-root sieve testing nearly $4$ billion candidate squares.
2. **Tangent planes at infinity:** A Lean-proved algebraic reduction and certified PARI/GP search over all rational tangent planes at infinity with parameter $1 \le n \le 250$, showing that only $(0, \pm 1, 1)$ appears.
3. **Complete classification of small fixed-$y$ fibers:** Reducing constant-$y$ slices to Mordell curves and filtering the published Bennett–Ghadermarzi tables determines every integer point with $|y| \le 27$ (and every even fiber with $|y| \le 78$).

## Three Lean-verified large integer solutions

Lean verifies the cubic equation and the bound $|x| > 30{,}000{,}000$ directly for all three triples in [WitnessSearch.lean](WitnessSearch.lean):

| $x$ | $y$ | $z$ |
| ---: | ---: | ---: |
| -280,813,200 | 157,750,309 | 889,840,366 |
| -71,709,552 | 18,357,983 | 1,094,157,121 |
| 36,307,388 | 16,351,199 | -179,013,631 |

## Searching by cube roots modulo $|z|$

### The congruence reduction

Set $d = |z|$. Rewriting the surface equation as $z(z + y^2) = 2 - x^3$ shows that every integer solution satisfies
$$
x^3 \equiv 2 \pmod d.
$$
For each cube root $r \in [0, d)$ of $2$ modulo $d$, write $x = r + qd$ ($q \in \mathbb{Z}$). Dividing through by $z = \pm d$ turns the equation into a single square test:
$$
y^2 = \left|\frac{r^3 - 2}{d} + d + 3r^2 q + 3rdq^2 + d^2 q^3\right|.
$$
The quantity inside the absolute value equals $(x^3 - 2)/d + d$: when it is positive, we recover a solution with $z = -d$; when it is negative, we recover a solution with $z = d$.

### Sieve implementation and search ranges

[witness_search.cpp](witness_search.cpp) constructs cube roots of $2$ modulo prime powers by Hensel lifting for primes $p > 3$ (there is no cube root of $2$ modulo $4$ or $9$, so $4 \nmid d$ and $9 \nmid d$) and combines them via the Chinese remainder theorem.

The table summarizes three search runs, where **Prime bound** caps the largest prime divisor of $d$, the $d$ range is inclusive, $|q| \le Q$, and the $|x|$ threshold is strict:

| Min $d$ | Max $d$ | Prime bound | $Q$ | Min $\lvert x\rvert$ | Root classes | Square tests |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 60,000,000 | 400,000 | 14 | 5,547,568 | 18,597,267 | 513,888,097 |
| 60,000,001 | 220,000,000 | 1,000,000 | 18 | 8,593,390 | 47,778,072 | 1,761,036,829 |
| 60,000,001 | 1,400,000,000 | 50,000 | 4 | 8,593,390 | 187,609,579 | 1,679,989,814 |

To compile and rerun all three searches:

```sh
g++ -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror witness_search.cpp -o /tmp/witness_search
/tmp/witness_search 60000000 400000 14 1 5547568
/tmp/witness_search 220000000 1000000 18 60000001 8593390
/tmp/witness_search 1400000000 50000 4 60000001 8593390
```

## Tangent planes at infinity

Homogenize the cubic surface as $X^3 + Y^2 Z + Z^2 T = 2T^3$. Every rational point at infinity has the form $[-a^2 b : a^3 : b^3 : 0]$ for coprime integers $a, b$.

1. **Integrality forces $a = \pm 1$.** An affine integer point $(x, y, z)$ lying on the tangent plane at $[-a^2 b : a^3 : b^3 : 0]$ satisfies
   $$
   3 a^4 b^2 x + 2 a^3 b^3 y + a^6 z + b^6 = 0.
   $$
   Hence $a \mid b^6$, forcing $a = \pm 1$ since $\gcd(a, b) = 1$. Rescaling sets $a = 1$ and $b = n$, giving the tangent plane
   $$
   z + 3n^2 x + 2n^3 y = -n^6.
   $$
2. **Exact reduction to a finite divisor check.** Put $m = -(3x + 2ny + n^4)$ and $A = x + m$. Then $z = n^2 m$, $x = A - m$, and $2ny = 2m - 3A - n^4$. Setting $H = n^8 + 6n^4 A - 3A^2$, substituting into the cubic equation and applying a Bézout identity yields
   $$
   mH = 4(2 - A^3), \qquad H \mid 4(n^{24} + 540n^{12} - 108), \qquad 3(A - n^4)^2 = 4n^8 - H.
   $$
3. **Exhaustion over $1 \le n \le 250$.** For every $n \ge 1$, the right-hand side $4(n^{24} + 540n^{12} - 108)$ is strictly positive. Listing all of its signed divisors $H$ and checking the square condition $3(A - n^4)^2 = 4n^8 - H$ recovers *every* integer point on that tangent plane.

Lean proves the algebraic reduction in [WitnessTangent.lean](WitnessTangent.lean), and the PARI/GP script [witness_tangent.gp](witness_tangent.gp) checks all $1 \le n \le 250$ using proven factorizations, finding **only** $(0, -1, 1)$ at $n = 1$. Negating $n$ simply negates $y$ (producing $(0, 1, 1)$ at $n = -1$), and at $n = 0$ the plane $z = 0$ forces $x^3 = 2$, which has no integer solutions.

## Fixed small ordinates ($y$ fixed)

Fixing $y$ turns $z^2 + y^2 z + x^3 = 2$ into a Mordell elliptic curve $Y^2 = X^3 + k$:

* **Even $y$:** Setting $(X, Y) = (-x,\, z + y^2/2)$ gives $Y^2 = X^3 + y^4/4 + 2$.
* **Odd $y$:** Setting $(X, Y) = (-4x,\, 4(2z + y^2))$ gives $Y^2 = X^3 + 16(y^4 + 8)$.

For every $|y| \le 27$, the constant term lies within the published [Bennett-Ghadermarzi Mordell tables](https://personal.math.ubc.ca/~bennett/BeGa-data.html). Filtering those tables by the substitutions above produces only
$$
x \in \{-32,\; -7,\; -2,\; 0,\; 1,\; 8,\; 20,\; 26\}.
$$
Extending the filter to even fibers $|y| \le 78$ yields a largest $|x|$ of **1,759**, achieved at $|y| = 32$. *(Trust boundary: this small-fiber classification relies on the published tables.)*
