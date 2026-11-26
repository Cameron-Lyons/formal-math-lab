# A quintic substitution on a Pell conic

Let $r$ and $q$ be functions on $u^2 - Dv^2 = 1$ with pole orders 1 and 2, respectively, at both points at infinity. For a nonzero rational $a$, set

$$
z = \frac{2 - r^3}{a}, \qquad x = r + qz.
$$

Then $x$ has pole order 5, and the cubic surface equation reduces to a single square condition:

$$
y^2 = a - z - 3r^2 q - 3rq^2 z - q^3 z^2.
$$

Lean verifies this polynomial reduction in [QuinticFactor.lean](QuinticFactor.lean). Finding a square on the right would produce infinitely many integer solutions whenever the family passes through an integer point and the Pell conic has infinitely many integer points.

**A natural choice that forces the leading term to be a square fails on every nonsplit Pell conic.** Put $q = -p^2$, where $p$ has pole order 1. The square condition rewrites as

$$
(2y - 2p^3 z + 3rp)(2y + 2p^3 z - 3rp) = 4(a - z) + 3r^2 p^2.
$$

Because $z$ has pole order 3, the right-hand side has pole order 4. The difference between the two factors on the left has pole order 6, so at least one factor has pole order at least 6. Every nonzero function regular away from the two conjugate ends has nonnegative pole order there (a negative pole order would give a nonconstant regular function on the projective conic), so the product cannot drop down to pole order 4. In [QuinticSquareObstruction.lean](QuinticSquareObstruction.lean), Lean verifies this obstruction for every irreducible quadratic denominator in the rational chart, with no height bound and no condition at 7.

There is also a height-free exclusion when $q$ is any quadratic polynomial in $r$, the marked point is $(0, 1, 1)$, and the marked value of $r$ lies in $\{0, 1, -1, 2, -2\}$. That argument bounds the odd-multiplicity roots on a double cover and eliminates both coefficients of $q$; see [QuinticInvariant.md](QuinticInvariant.md).

## A necessary condition at 7

Assume $D$ and $a$ are 7-adic units and $r, q$ are 7-integral in the Pell basis. **For every choice of seed, the square condition forces $r$ to reduce to a constant modulo 7.** This covers every reduction of $q$, including constant and zero. Exact FLINT arithmetic in [quintic_factor_search.py](quintic_factor_search.py) runs 1,714,314 square tests for the split square class of $D \bmod 7$ and 1,411,788 for the nonsplit class, with zero squares found.

To cut down the search space, write $r = h + mu + nv$. Shifting along the norm-1 torus fixes $h$ and $N = m^2 - n^2/D$, and acts transitively on all pairs $(m, n)$ with a given $N \ne 0$ (the ratio of two elements of norm $N$ in the split or nonsplit quadratic algebra has norm 1). Multiplying both $r$ and $q$ by a cube root of unity $\zeta$ preserves $z$ and the square condition while sending $(h, N) \mapsto (\zeta h, \zeta^2 N)$. Together these symmetries leave $7 \cdot 6 / 3 = 14$ orbits with $N \ne 0$. In the split case, $N = 0$ also allows nonzero $(m, n)$, and adding the reflection $v \mapsto -v$ leaves 3 extra orbits. The script builds these orbits explicitly and confirms that they cover all $7(7^2 - 1)$ nonconstant linear polynomials $r$.

For each orbit representative, the script tests all 6 nonzero values of $a$ and all $7^5$ quadratics

$$
q = q_0 + q_1(u - 1) + q_2 v + c(u - 1)^2 + e(u - 1)v.
$$

Why is testing mod-7 reductions valid with no assumption on $y$? Any rational $y$ solving the equation has pole order at most 6. In the $t$-chart with $L_D = 1 - Dt^2$, multiplying the right-hand side by $L_D^{12}$ gives a 7-integral polynomial. A rational function whose square is a 7-integral polynomial must itself be a 7-integral polynomial (by unique factorization in $\mathbb{Q}[t]$ and multiplicativity of the Gauss norm), so its reduction modulo 7 would have to pass the census.

## A rational search also allowing lost poles

We also ran two bounded rational searches in [quintic_factor_search.py](quintic_factor_search.py) that allow $r$ to reduce to a constant modulo 7. At each of the three seeds $(0, 1, 1)$, $(1, 0, 1)$, and $(-2, 3, 1)$, we try $r_0 = r(1, 0) \in \{-1, 0, 1, 2\}$ and set $a = 2 - r_0^3$ and $q_0 = x_0 - r_0$ so that $x$ and $z$ match the seed. Write

$$
r = r_0 + \frac{A(u - 1) + Bv}{d}, \qquad
q = q_0 + \frac{C(u - 1) + Ev + F(u - 1)^2 + G(u - 1)v}{d}.
$$

At either end of the conic, the leading term of $y^2$ is $-q^3 z^2$, so $-(F + G/\sqrt{D})/d$ must be a square in $\mathbb{Q}(\sqrt{D})$.

* With all six numerators in $[-2, 2]$ and lowest-terms common denominator $1 \le d \le 3$ across every squarefree $2 \le D \le 30$, exactly 272,448 tuples have the required pole orders and pass the leading square test. None survives the polynomial square tests at the applicable primes $5, 7, 11, 13, 17$.
* To target cases outside the mod-7 exclusion, a second search takes numerators in $[-3, 3]$ with $d \in \{7, 49\}$ for every squarefree $2 \le D \le 50$, plus $d = 1$ whenever $7 \mid D$. Of the 1,128,960 tuples passing the leading square test, none survives the polynomial square tests.

To reproduce all three computations, run:

```sh
uv run --with python-flint==0.9.0 python quintic_factor_search.py --mod7
uv run --with python-flint==0.9.0 python quintic_factor_search.py
uv run --with python-flint==0.9.0 python quintic_factor_search.py --height 3 --max-D 50 --at-seven
```
