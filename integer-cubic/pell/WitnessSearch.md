# Integer points and tangent planes

Three explicit integer solutions to $z^2 + y^2 z + x^3 = 2$ have distinct $x$-coordinates with $|x| > 30{,}000{,}000$. Lean checks each equation and inequality directly in [WitnessSearch.lean](WitnessSearch.lean):

| $x$ | $y$ | $z$ |
| ---: | ---: | ---: |
| -280,813,200 | 157,750,309 | 889,840,366 |
| -71,709,552 | 18,357,983 | 1,094,157,121 |
| 36,307,388 | 16,351,199 | -179,013,631 |

## Search by cube roots

Set $d = |z|$. Any integer solution satisfies $x^3 \equiv 2 \pmod d$. For each cube root $0 \le r < d$, write $x = r + qd$. Then $y^2$ must equal

$$
y^2 = \left|\frac{r^3 - 2}{d} + d + 3r^2 q + 3rdq^2 + d^2 q^3\right|.
$$

The expression inside the absolute value is $(x^3 - 2)/d + d$; when it is positive we get $z = -d$, and when it is negative we get $z = d$.

[witness_search.cpp](witness_search.cpp) builds cube roots modulo prime powers by Hensel lifting for primes $p > 3$ (there is no root modulo 4 or 9) and combines them with the Chinese remainder theorem. The table summarizes three search runs, where the prime bound limits the largest prime divisor of $d$, the $d$ range is inclusive, $|q| \le Q$, and the $|x|$ threshold is strict:

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

Homogenize the cubic surface as $X^3 + Y^2 Z + Z^2 T = 2T^3$. At a rational point at infinity $[-a^2 b : a^3 : b^3 : 0]$ with coprime integers $a, b$, an affine integer point $(x, y, z)$ on the tangent plane satisfies

$$
3 a^4 b^2 x + 2 a^3 b^3 y + a^6 z + b^6 = 0.
$$

Thus $a \mid b^6$, forcing $a = \pm 1$. Rescaling sets $a = 1$ and $b = n$, so the tangent plane is $z + 3n^2 x + 2n^3 y = -n^6$. Put $m = -(3x + 2ny + n^4)$ and $A = x + m$. Then $z = n^2 m$, $x = A - m$, and $2ny = 2m - 3A - n^4$. Setting $H = n^8 + 6n^4 A - 3A^2$, substitution and a Bézout identity yield

$$
mH = 4(2 - A^3), \qquad H \mid 4(n^{24} + 540n^{12} - 108), \qquad 3(A - n^4)^2 = 4n^8 - H.
$$

For every $n \ge 1$, the integer on the right of the divisibility is positive. Listing its signed divisors and checking the square condition recovers all integer points on that tangent plane. Lean proves the algebraic reduction in [WitnessTangent.lean](WitnessTangent.lean), and the PARI/GP script [witness_tangent.gp](witness_tangent.gp) checks all $1 \le n \le 250$ using proven factorizations, finding only $(0, -1, 1)$ at $n = 1$. Negating $n$ simply negates $y$, and at $n = 0$ the plane $z = 0$ forces $x^3 = 2$, which has no integer solutions.

## Fixed small ordinates

For fixed even $y$, setting $(X, Y) = (-x, z + y^2/2)$ gives $Y^2 = X^3 + y^4/4 + 2$. For fixed odd $y$, setting $(X, Y) = (-4x, 4(2z + y^2))$ gives $Y^2 = X^3 + 16(y^4 + 8)$. For all $|y| \le 27$, the constant term falls inside the published [Bennett-Ghadermarzi Mordell tables](https://personal.math.ubc.ca/~bennett/BeGa-data.html). Filtering those tables by the substitutions above gives only $x \in \{-32, -7, -2, 0, 1, 8, 20, 26\}$. Extending the check to even fibers $|y| \le 78$ gives a largest $|x|$ of 1,759, achieved at $|y| = 32$. This small-fiber classification relies on the published tables.
