# A quintic substitution on a Pell conic

Take functions \(r,q\) on \(u^2-Dv^2=1\), of pole orders one and two at both points at infinity. For a nonzero rational \(a\), set

\[
 z=(2-r^3)/a,\qquad x=r+qz .
\]

Then \(x\) has pole order five. The remaining condition is the single square

\[
 y^2 = a-z-3r^2q-3rq^2z-q^3z^2 .
\]

Lean verifies the polynomial identity giving this reduction. A square on the right would produce the desired family if it includes an integral point and the Pell conic has infinitely many integral points. [Substitution identity](QuinticFactor.lean)

**One natural way to make the leading term a square fails for every nonsplit Pell conic.** Take \(q=-p^2\) with \(p\) of pole order one. The square condition implies

\[
(2y-2p^3z+3rp)(2y+2p^3z-3rp)=4(a-z)+3r^2p^2 .
\]

The right side has pole order four because \(z\) has order three. The difference of the two factors has order six, so at least one factor has order six or more. Every nonzero rational function regular away from the two conjugate ends has nonnegative pole order there: a negative order would give a nonconstant function regular everywhere on the projective conic. The product therefore cannot have order four. Lean checks this argument for any irreducible quadratic denominator in the rational chart, without a bound on the coefficients or any condition at 7. [Formal exclusion](QuinticSquareObstruction.lean)

There is also an exact exclusion when \(q\) is any quadratic polynomial in \(r\), the marked cubic point is \((0,1,1)\), and the marked value of \(r\) belongs to \(\{0,1,-1,2,-2\}\). It follows by bounding the number of odd-multiplicity roots of the required square on a double cover and eliminating the two coefficients of \(q\). [Discriminant calculation](QuinticInvariant.md)

## A necessary condition at 7

Assume \(D,a\) are 7-adic units and \(r,q\) are integral at 7 in the Pell basis. **The required square forces \(r\) to reduce to a constant, for every choice of seed.** This includes all possible reductions of \(q\), including constant and zero. The split and nonsplit squareclasses of \(D\bmod7\) give 1,714,314 and 1,411,788 polynomial square tests respectively, each with zero squares. This part uses exact FLINT arithmetic over \(\mathbb F_7\). [Finite-field census](quintic_factor_search.py)

Write \(r=h+mu+nv\). Translation by a point of the norm-one torus preserves \(h\) and \(N=m^2-n^2/D\), and acts transitively on the pairs with a given \(N\ne0\). Indeed the ratio of two elements of norm \(N\) in the split or nonsplit quadratic algebra has norm one. Multiplying \(r,q\) by a cube root of unity leaves \(z\) and the square condition unchanged and carries \((h,N)\) to \((\zeta h,\zeta^2N)\). These actions give \(7\cdot6/3=14\) choices with \(N\ne0\). In the split case \(N=0\) also allows a nonzero \((m,n)\); including the reflection \(v\mapsto-v\) gives three more orbits. The checker constructs the orbits explicitly and checks that they cover all \(7(7^2-1)\) nonconstant linear \(r\). For each representative, test all six nonzero \(a\) and all \(7^5\) quadratics

\[
 q=q_0+q_1(u-1)+q_2 v+c(u-1)^2+e(u-1)v
\]

with arbitrary coefficients. If a rational \(y\) existed, its poles would have order at most six. In \(t\)-coordinates the square test multiplies the right-hand side by \(L_D^{12}\), where \(L_D=1-Dt^2\). The result is an integral polynomial. A rational function whose square is an integral polynomial must itself be a polynomial and be integral at 7, by unique factorization over \(\mathbb Q[t]\) and multiplicativity of the coefficient Gauss norm. Its reduction would pass the finite test.

## A rational search also allowing lost poles

At each of \((0,1,1),(1,0,1),(-2,3,1)\), set \(r_0=r(1,0)\) to \(-1,0,1,2\) in turn. Take \(a=2-r_0^3\) and \(q_0=x_0-r_0\), which imposes the required \(x,z\) at the seed. The search takes

\[
 r=r_0+\frac{A(u-1)+Bv}{d},\qquad
 q=q_0+\frac{C(u-1)+Ev+F(u-1)^2+G(u-1)v}{d},
\]

with the six numerators between \(-2\) and 2 and a common denominator \(1\le d\le3\) in lowest terms. It tests every squarefree \(2\le D\le30\). At either end the leading term of \(y^2\) is \(-q^3z^2\). Therefore \(-(F+G/\sqrt D)/d\) must be a square in \(\mathbb Q(\sqrt D)\). Exactly 272,448 parameter tuples meet this leading test with \(r,q\) of the stated orders. No tuple survives the polynomial square tests at the applicable primes \(5,7,11,13,17\). [Rational search](quintic_factor_search.py)

A second search targets cases outside the mod-7 exclusion. It allows numerators between \(-3\) and 3 and denominators \(d=7,49\) for all squarefree \(2\le D\le50\), together with \(d=1\) when \(7\mid D\). Of the 1,128,960 parameter tuples passing the leading test, none survives the polynomial square tests.

~~~sh
uv run --with python-flint==0.9.0 python quintic_factor_search.py --mod7
uv run --with python-flint==0.9.0 python quintic_factor_search.py
uv run --with python-flint==0.9.0 python quintic_factor_search.py --height 3 --max-D 50 --at-seven
~~~
