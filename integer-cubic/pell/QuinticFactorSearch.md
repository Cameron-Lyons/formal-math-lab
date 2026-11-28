# A quintic substitution on a Pell conic

One structured way to search for infinitely many integer solutions to $z^2 + y^2 z + x^3 = 2$ on a Pell conic $u^2 - Dv^2 = 1$ is to choose a **quintic** ansatz ($x$ of pole order $5$ at infinity) that makes $2 - x^3$ automatically divisible by $z$, collapsing the cubic surface equation to a single polynomial square condition for $y^2$.

This note proves two obstructions and records two bounded searches for this quintic family:

1. **Height-free obstruction for $q = -p^2$:** The most natural specialization that makes the leading term of $y^2$ a square is impossible on *every* nonsplit Pell conic, formalized in Lean with no height bound and no prime hypothesis.
2. **Mod-7 degeneracy condition:** Whenever $D$ and the scaling constant $a$ are $7$-adic units and the inputs $r, q$ are $7$-integral, an exhaustive search over more than $3.1$ million cases modulo $7$ proves that **$r$ must reduce to a constant modulo $7$**—regardless of the seed.
3. **Bounded rational searches:** Over $1.4$ million rational candidates (explicitly allowing lost poles and $7$-degenerate reductions) yield zero solutions.

## The quintic reduction

Let $r$ and $q$ be rational functions on the Pell conic $u^2 - Dv^2 = 1$ that are regular away from the two points at infinity and have pole orders $1$ and $2$ there, respectively. For a nonzero rational constant $a$, set
$$
z = \frac{2 - r^3}{a}, \qquad x = r + qz.
$$
Because $z$ has pole order $3$ and $q$ has pole order $2$, $x$ has pole order $5$. Expanding $2 - x^3 = 2 - (r + qz)^3$ replaces $2 - r^3$ by $az$, so $z$ divides out cleanly and the cubic surface equation $z(z + y^2) = 2 - x^3$ reduces to a single square condition:
$$
y^2 = a - z - 3r^2 q - 3rq^2 z - q^3 z^2.
$$
Lean verifies this polynomial reduction in [QuinticFactor.lean](QuinticFactor.lean). Finding a rational square on the right-hand side would generate infinitely many integer solutions whenever the family passes through an integer point and the Pell conic has infinitely many integer points.

## Height-free obstructions

### 1. Why the leading-square choice $q = -p^2$ fails everywhere

Looking at the highest-order term $-q^3 z^2$ of $y^2$, the most natural way to guarantee a leading square is to put $q = -p^2$, where $p$ has pole order $1$ at both ends of the conic (making $-q^3 z^2 = (p^3 z)^2$).

**This choice fails on every nonsplit Pell conic.** Completing the square on the $p^6 z^2$ and $3r p^4 z$ terms rewrites the square condition as a difference of squares:
$$
(2y - 2p^3 z + 3rp)(2y + 2p^3 z - 3rp) = 4(a - z) + 3r^2 p^2.
$$
Now compare pole orders at the two conjugate ends at infinity:

1. **Right-hand side:** $z$ has pole order $3$ and $r^2 p^2$ has pole order $4$, so the right-hand side has pole order $4$.
2. **Difference of the left-hand factors:** Subtracting the two factors gives $4p^3 z - 6rp$, which has pole order $6$. Consequently, at least one of the two factors on the left has pole order at least $6$.
3. **No cancellation of poles is possible:** Every nonzero function that is regular away from the two conjugate ends must have *nonnegative* pole order there (a negative pole order would mean a zero at infinity with no poles anywhere, yielding a nonconstant regular function on the projective conic).

Therefore the product on the left has pole order at least $6$, which can never equal the right-hand side of pole order $4$. In [QuinticSquareObstruction.lean](QuinticSquareObstruction.lean), Lean verifies this obstruction for every irreducible quadratic denominator in the rational chart, with no height bound and no condition at $7$.

### 2. Quadratic $q(r)$ at small marked values

There is also a height-free exclusion whenever $q$ is *any* quadratic polynomial in $r$, the marked point is $(0, 1, 1)$, and the marked value of $r$ lies in $\{0, 1, -1, 2, -2\}$. That argument bounds the odd-multiplicity roots on a double cover and eliminates both free coefficients of $q$; see [QuinticInvariant.md](QuinticInvariant.md).

## A necessary condition at 7

Assume $D$ and $a$ are $7$-adic units and $r, q$ are $7$-integral in the Pell basis. **For every choice of seed, the square condition forces $r$ to reduce to a constant modulo $7$.** This holds for every reduction of $q$, including constant and zero reductions.

Exact FLINT arithmetic in [quintic_factor_search.py](quintic_factor_search.py) runs **1,714,314** square tests for the split square class of $D \bmod 7$ and **1,411,788** for the nonsplit class, with **zero** squares found.

### Symmetry reduction of the mod-7 search

Write a general pole-$1$ function as $r = h + mu + nv$. Two symmetries drastically shrink the search space:

* **Norm-1 torus shifts** on the conic fix $h$ and the norm $N = m^2 - n^2/D$, and act transitively on all pairs $(m, n)$ sharing a given $N \ne 0$ (the ratio of two elements of norm $N$ in either the split or nonsplit quadratic algebra has norm $1$).
* **Cube-root scaling** $(r, q) \mapsto (\zeta r, \zeta q)$ (where $\zeta^3 = 1$ in $\mathbb{F}_7$) preserves $z = (2 - r^3)/a$ and the square condition while sending $(h, N) \mapsto (\zeta h, \zeta^2 N)$.

Together these symmetries reduce all nonconstant $r$ with $N \ne 0$ to $7 \cdot 6 / 3 = 14$ orbits. In the split case, $N = 0$ also permits nonzero $(m, n)$, and adding the reflection $v \mapsto -v$ leaves $3$ extra orbits. The script constructs these orbits explicitly and confirms that they cover all $7(7^2 - 1)$ nonconstant linear polynomials $r$.

For each orbit representative, the script tests all $6$ nonzero values of $a \in \mathbb{F}_7^\times$ and all $7^5$ quadratics
$$
q = q_0 + q_1(u - 1) + q_2 v + c(u - 1)^2 + e(u - 1)v.
$$

### Why no 7-integrality assumption on $y$ is needed

Any rational $y$ satisfying the square condition has pole order at most $6$. Passing to the rational $t$-chart with denominator $L_D = 1 - Dt^2$ and multiplying the right-hand side by $L_D^{12}$ yields a $7$-integral polynomial. By unique factorization in $\mathbb{Q}[t]$ and multiplicativity of the Gauss norm, any rational function whose square is a $7$-integral polynomial must itself be a $7$-integral polynomial—so its reduction modulo $7$ would have to appear in the census.

## Bounded rational searches allowing lost poles

To probe solutions outside the mod-$7$ exclusion (where $r$ drops to a constant modulo $7$, or $7 \mid D$), [quintic_factor_search.py](quintic_factor_search.py) runs two bounded rational searches.

At each of the three seeds $(x_0, y_0, z_0) \in \{(0, 1, 1),\, (1, 0, 1),\, (-2, 3, 1)\}$, choose a marked value $r_0 = r(1, 0) \in \{-1, 0, 1, 2\}$ and set $a = 2 - r_0^3$ and $q_0 = x_0 - r_0$ so that $x$ and $z$ hit the seed automatically. Parameterize
$$
r = r_0 + \frac{A(u - 1) + Bv}{d}, \qquad
q = q_0 + \frac{C(u - 1) + Ev + F(u - 1)^2 + G(u - 1)v}{d}.
$$
At either end of the conic, the leading term of $y^2$ is $-q^3 z^2$, which forces $-(F + G/\sqrt{D})/d$ to be a square in $\mathbb{Q}(\sqrt{D})$—a fast initial filter before running polynomial square tests.

* **General small-height search:** Taking all six numerators $A, B, C, E, F, G \in [-2, 2]$ and lowest-terms common denominator $1 \le d \le 3$ across every squarefree $2 \le D \le 30$, exactly **272,448** tuples have the required pole orders and pass the leading square test. None survives the polynomial square tests at the applicable primes $5, 7, 11, 13, 17$.
* **Targeted search at 7:** To focus specifically on cases escaping the mod-$7$ theorem, a second search takes numerators in $[-3, 3]$ with $d \in \{7, 49\}$ across every squarefree $2 \le D \le 50$, plus $d = 1$ whenever $7 \mid D$. Of the **1,128,960** tuples passing the leading square test, none survives the polynomial square tests.

## Reproduction

```sh
uv run --with python-flint==0.9.0 python quintic_factor_search.py --mod7
uv run --with python-flint==0.9.0 python quintic_factor_search.py
uv run --with python-flint==0.9.0 python quintic_factor_search.py --height 3 --max-D 50 --at-seven
```
