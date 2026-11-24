# Quartic Pell substitutions through one integer point

Use the parameter \(t\) on \(u^2-3v^2=1\), with \(L=1-3t^2\), \(u=(1+3t^2)/L\) and \(v=2t/L\). The sought substitution through \((0,1,1)\) at \(t=0\) is

\[
 (x,y,z)=(X/L^4,Y/L^3,Z/L^6), \qquad X^3+ZY^2+Z^2=2L^{12}.
\]

Here \(X,Y,Z\) are rational polynomials of degrees at most \(8,6,12\), have constant terms \(0,1,1\), and \(X\ne0\). Lean proves that **any** such identity implies infinitely many integer solutions. The theorem also accepts any integral seed, with the corresponding nonconstancy assumption. The proof uses a subsequence of powers of \(2+\sqrt3\) to clear the coefficient denominators while preserving the chosen seed modulo those denominators. [Lean theorem](MixedPellAmplification.lean)

## Descent from the singular residues at 7

Assume the coefficients are integral at 7 and \(\gcd(\bar X,\bar L)=1\). Of the 66 possible triples modulo 7, 48 have Jacobian rank 20. Exactly 4,410 triples modulo 49 over those 48 classes extend modulo 343. **2,352 of the 4,410 cannot arise from rational identities of any coefficient height.** The counts and ranks below are exact FLINT calculations. Lean checks the characteristic-zero descent used in the last step. [First lift enumeration](quartic_first_lifts.py) · [Classification modulo 49](quartic_free_mark.py) · [Lean descent](QuarticPullbackDescent.lean)

To identify the 2,352 classes, let \(S=(ct+dt^2)/L\) and set

\[
 x=3S^4+bS,\qquad y=1+C S^3,\qquad z=1+F S^3+E S^6 .
\]

The identity is equivalent for nonconstant \(S\) to the four equations

\[
\begin{aligned}
 b^3+2C+3F&=0,\\
 3E+(F+C)^2+9b^2&=0,\\
 2(F+C)E+C^2F+27b&=0,\\
 E^2+C^2E+27&=0 .
\end{aligned}
\]

At \((b,C,F,E)=(0,3,-2,2)\bmod 7\) the Jacobian is invertible. Hensel lifting gives coefficients in \(\mathbb Z_7\), equal to \((14,38,40,30)\bmod 49\). In particular \(bC\ne0\). Every rank-20 residue is obtained from one of these compositions modulo 7, up to \(t\mapsto-t\) and a cube-root-of-unity multiple of \(x\). For each choice of \((c,d)\bmod 7\), its 49 lifts modulo 49 give distinct triples. Multiplication by the orbit sizes gives \(48\cdot49=2,352\).

It remains to show that **every** exact solution reducing to one of these triples is of the indicated form. For \(c\ne0\bmod 7\), use the coefficients \(Y_3,Y_4\) as coordinates. Their variable parts are \(Cc^3,3Cc^2d\). For \(c=0\bmod7\) use \(Y_5,Y_6\), with variable parts \(3Ccd^2,Cd^3\) and \(d\ne0\bmod7\). Each pair has invertible Jacobian in \(c,d\), so a composition can be chosen to match the two coefficients of any proposed exact lift. Its other coefficients then agree with the proposed lift modulo 49 because those two coordinates distinguish the 49 compositions.

Fix these coordinates and write \(M\) for the Jacobian in the remaining 24 unknowns. In every listed mod-49 class, its rank modulo 7 is 20 and \(v_7(\det M)=4\). Thus \(7M^{-1}\) has integral entries. This property persists when \(M\) changes by a multiple of 49, since \(M^{-1}(M'-M)\) is divisible by 7. If two solutions with the same fixed coordinates differ by a vector \(\Delta\) divisible by \(7^k\), \(k\ge2\), Taylor expansion gives \(M\Delta\in7^{2k}\mathbb Z_7^{24}\), hence \(\Delta\in7^{2k-1}\mathbb Z_7^{24}\). Iteration proves equality.

For a rational chart, choose two rational parameters where \(r=y-1\) takes distinct nonzero rational values. The accompanying values of \(z\) are rational, and

\[
 z-1=(F/C)r+(E/C^2)r^2 .
\]

The two evaluations imply \(k=F/C,\ \ell=E/C^2\in\mathbb Q\). Now \(g=b^3/C=-2-3k\) is rational and nonzero. On setting \(T=bS\), the sparse identity has rational coefficients

\[
 x=T-\frac{3\ell+(k+1)^2}{3g^2}T^4,\quad
 y=1+T^3/g,\quad z=1+(k/g)T^3+(\ell/g^2)T^6 .
\]

The same computation applies after multiplying \(x\) by a cube root of unity, using its new linear coefficient in the definition of \(T\). The Lean descent proves that these coefficient equations contradict the rational sparse-quartic obstruction. The 2,058 remaining singular classes and the 18 rank-24 classes modulo 7 require other arguments. [Rational sparse obstruction](QuarticSparse.lean)

**Consequence for substitutions with \(x\) a function of \(u\) alone.** Suppose \(D\) is a 7-adic unit with nonsquare residue, and use \(u^2-Dv^2=1\) with \(L_D=1-Dt^2\) and the same seed. Assume the coefficients are integral at 7 and the two poles of \(x\) retain order four modulo 7. Then \(x\) cannot be a polynomial in \(u\) alone. Indeed \(D/3\) is a square in \(\mathbb Z_7^\times\). Rescaling \(t\) by a square root identifies the charts at 7 and preserves evenness of the abscissa numerator. Of the twelve residue orbits, only the singular representatives \((c,d)=(0,1),(0,6),(1,0)\) have even \(X\) modulo 7. In the first two every lift is a sparse composition. In the third, all 49 noncomposition classes have \(X_1=14\bmod49\) before symmetry. Twisting or reflecting preserves nonvanishing of \(X_1\). This forces an even abscissa into the sparse composition. The descent uses two rational values of the original \(y,z\), so it applies even when the change of parameter itself is only 7-adic.

## Bounded searches on the remaining classes

For each of the seven singular orbit representatives with remaining classes, fix \(Y_3,Y_4\) to every pair of admissible fractions of individual height at most 16. Lifting to 46 base-7 digits and rationally reconstructing with height bound \(10^{18}\) on the other individual coefficients gives zero identities among 10,803 parameter pairs. All three twists of \(x\) are covered. [Rational slice checker](quartic_free_mark.py)

One can instead bound only \(x\), allowing \(y,z\) coefficients of arbitrary height. The smooth residue classes and the remaining singular classes give 144,060 distinct abscissa vectors modulo 343 after symmetry. For a smooth class, the checker solves for the triple for all choices of the two free coefficients modulo 343. In a remaining singular class, two exact solutions over the same mod-49 triple satisfy \(M\Delta_{\rm fixed}+N\Delta_{\rm free}=0\bmod49^2\), with \(N\) the two omitted columns. Since \(7M^{-1}\) is integral, this determines the abscissa modulo 343 as an affine function of the two free digits. In fact \(M^{-1}N\) is integral, since each column of \(N\) is in the image of \(M\bmod 7\) and \(7M^{-1}\) is integral. [Search implementation](quartic_free_abscissas.py)

In each coordinate system write the eight coefficients with a common positive denominator \(d\) in lowest terms. Their height is \(\max(d,|a_1|,\ldots,|a_8|)\). The first basis uses the numerator coefficients of \(X\). The second expands \(x\) in \((u-1)^i,\ 1\le i\le4\), and \(v(u-1)^j,\ 0\le j\le3\). At height 171, each residue modulo 343 times \(d\) has one centered representative per coefficient. At any tested odd prime coprime to \(d\), both factors of \(Z(Z+Y^2)=2L^{12}-X^3\) have integral coefficients. This follows from multiplicativity of the Gauss norm and their unit constant terms. Factoring the right side and testing complementary factors for a square difference is therefore a necessary test even with unrestricted denominators for \(Y,Z\). [Integer vector sieve](quartic_free_abscissas.cpp) · [Factor and square test](quartic_rational_search.py)

| Basis at height 171 | Primitive vectors after the mod-343 test | After testing at 3 and 5 where applicable | After also testing at 13, 11, 17 and 19 |
| --- | ---: | ---: | ---: |
| Numerator | 21,132,628 | 1,610,292 | 0 |
| Pell | 21,134,654 | 2,407,006 | 0 |

These are counts within each basis and may include the same rational abscissa in both. The bound applies to \(x\) only.

## Changing the Pell conic and the integral seed

For squarefree positive \(D>1\), use \(L_D=1-Dt^2,\ u=(1+Dt^2)/L_D,\ v=2t/L_D\). Repeat the factor-and-square test at each of \((0,1,1),(1,0,1),(-2,3,1)\). In both searches \(y,z\) may use all the mixed terms allowed by the original degree bounds. A prime dividing the common denominator of \(x\) is skipped. These searches impose no pole-retention hypothesis at 7.

* With \(x=x_0+\sum_{i=1}^4 a_i(u-1)^i/d\) of exact degree four and height at most six, there are 151,010 primitive vectors for each seed. On all 18 squarefree conics \(2\le D\le30\) the congruence tests exclude every vector. [Search with \(x\) depending only on \(u\)](even_abscissa_search.py)
* Allow all eight basis terms of \(x-x_0\), with numerators in \(\{-1,0,1\}\) and \(1\le d\le6\). Require a nonzero \(v\)-term and at least one order-four term. This gives 34,668 vectors per seed. The congruence tests exclude all of them on the 49 squarefree conics \(2\le D\le80\). [Mixed-coefficient search](mixed_conic_search.py)

Run these commands from this directory.

~~~sh
uv run --with python-flint==0.9.0 python quartic_free_mark.py --height 16
uv run --with python-flint==0.9.0 python quartic_free_abscissas.py --height 171
uv run --with python-flint==0.9.0 python even_abscissa_search.py
uv run --with python-flint==0.9.0 python mixed_conic_search.py
lake -d .. build
~~~
