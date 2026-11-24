# Uniform exclusion of positive-slope cubic substitutions at 7

Suppose $X,Y,Z\in\mathbb Q[t]$ have degree at most six and constant terms $(0,1,1)$ or $(-2,3,1)$. Put $Q=1-Dt^2$, with $D$ a nonzero integer. If
$$
X^3+ZY^2+Z^2Q^3=2Q^9,
$$
then every coefficient of $X,Y,Z$ is integral at 7. The same conclusion holds for the seeds $(1,0,1)$ and $(1,0,-1)$. This includes $D=3$ and closes both positive-slope cases left by the finite-precision computations. [Earlier obstruction series](cubic_chart_obstructions.md)

## The two scales

If a coefficient is nonintegral, take the maximum of $-v_7(f_i)/i$ over nonzero coefficients with $i>0$. Denote this positive rational number by $h$. Substitute $7^h t$ for $t$, using a finite totally ramified extension for the required fractional power of 7. The rescaled polynomials are integral and some nonconstant term survives reduction. Their denominator is $1-Ct^2$, where $C=D7^{2h}$ has positive valuation. Reduction gives an ordinary polynomial solution $x^3+zy^2+z^2=2$ over $\mathbb F_7$. Enumerating all $7^6$ nonconstant coefficient vectors for $x$, including the zero vector, and all allowed divisors $z\mid 2-x^3$ yields six nonconstant triples at the first seed and 42 at the second. Each seed $(1,0,\pm1)$ gives 18 additional nonconstant triples. Every one has $\deg y=3$ and $\deg z=6$. The checker verifies these two facts directly before any chart normalization. [Exhaustive residue check](cubic_annulus_residues.py)

The following argument works over any discretely valued field with residue characteristic different from 2 and 3. Write $A(s)=s^6X(1/s)$, $B(s)=s^6Y(1/s)$ and $E(s)=s^6Z(1/s)$ for the reversals of the balanced numerators. Write $B_i=[s^i]B(s)$. Then $E(0)$ and $B_3$ are units, and $B_0,B_1,B_2$ have positive valuation when nonzero. The reversed equation is
$$
A^3+EB^2+E^2(s^2-C)^3=2(s^2-C)^9.
$$
Choose
$$
r=\min\left\{\tfrac12v(C),\,v(B_0)/3,\,v(B_1)/2,\,v(B_2)\right\}>0
$$
with $v(0)=+\infty$. In a totally ramified extension choose $\lambda$ of valuation $r$. Substitute $s=\lambda T$ and set
$$
A_1=A(\lambda T)/\lambda^2,\quad B_1^*=B(\lambda T)/\lambda^3,\quad E_1=E(\lambda T),\quad c_1=C/\lambda^2.
$$
The polynomials $B_1^*,E_1$ and the scalar $c_1$ are integral by construction. The scaled equation gives
$$
A_1^3=2\lambda^{12}(T^2-c_1)^9-E_1(B_1^*)^2-E_1^2(T^2-c_1)^3.
$$
Consequently $A_1$ is integral too. Indeed a polynomial whose least coefficient valuation is $m$ has cube of least coefficient valuation $3m$, since the normalized polynomial has nonzero reduction and its cube remains nonzero. The general integrally closed ring version is checked in Lean. [Polynomial integrality and specialization](CubicAnnulus.lean)

Let $a,b,e,c$ be the reductions of $A_1,B_1^*,E_1,c_1$. Then $e$ is a nonzero constant and $b=b_0+b_1T+b_2T^2+b_3T^3$ with $b_3\ne0$. Every coefficient at exponent greater than three disappears because its scaling factor is a positive power of $\lambda$. The reduced equation is
$$
a^3+e b^2+e^2(T^2-c)^3=0.
$$
Either $c\ne0$, or at least one of $b_0,b_1,b_2$ is nonzero. This follows from the minimum defining $r$.

## Both reduced equations are impossible

For a field $k$ of characteristic different from 2 and 3 and $e\ne0$, the equation $x^3+ey^2=-e^2$ has only constant solutions in $k(T)$. Clearing reduced denominators gives the polynomial Fermat–Catalan equation with exponents $2,6,3$. Mathlib's theorem includes its positive-characteristic descent. [Lean constant-fiber theorem](PellConstantFiber.lean)

If $c=0$, take $x=a/T^2$ and $y=b/T^3$. The constant-fiber theorem forces $b$ to be a scalar multiple of $T^3$. This contradicts the surviving lower coefficient.

If $c\ne0$, parametrize $d^2=s^2-c$ by $s=(w^2+c)/(2w)$ and $d=(w^2-c)/(2w)$. Now $x=a(s)/d^2$ and $y=b(s)/d^3$ satisfy the same constant-fiber equation in $k(w)$. Write $y=k_0$ and clear denominators in $b(s)=k_0 d^3$. The coefficient of $w^6$ gives $b_3=k_0$. The constant coefficient gives $b_3c^3=-k_0c^3$. Since $c,b_3$ and 2 are nonzero, these identities contradict each other. Lean checks both reduced contradictions. [Inner and denominator radius proofs](CubicAnnulus.lean)

The construction of fractionally valued scaling elements and the identification of the resulting coefficients with the reductions above are the written parts of the proof. FLINT checks the exhaustiveness of the finite list. Lean verifies the maximum defining the first radius, the minimum defining the second radius, cube integrality, specialization of the scaled identity, and both residue contradictions. [First radius](PoleTwoReduction.lean) · [Second radius and reduced equations](CubicAnnulus.lean)

```sh
uv run --with python-flint==0.9.0 cubic_annulus_residues.py
lake -d .. build CubicAnnulus
```
