# A quartic Pell substitution through the seed cannot have an odd integral second abscissa

Suppose a rational polynomial substitution on $u^2-3v^2=1$ has coordinate degrees at most $4,3,6$, takes $(1,0)$ to $(0,1,1)$, and satisfies $x^3+y^2z+z^2=2$ identically. If all three coordinates of its value at $(2,1)$ are integral at 2, its $x$ coordinate there must be even. This excludes the proposed second endpoint $(1,0,-1)$ and every odd integral abscissa. The coefficients of the substitution may have arbitrary rational denominators.

## Balancing denominators at both marks

Write $w=u-1-v$. Then $v^2=(1+w)v+w+w^2/2$. Each coordinate of degree at most $d$ has a unique representation $P(w)+vQ(w)$ with degrees at most $d,d-1$. Existence follows by eliminating $v^2$, which preserves the total-degree bound. Uniqueness follows by division by the monic quadratic in $v$. Both marks have $w=0$. For a first coordinate value $c$ at the seed and a corresponding second value $b$, the constants are $P(0)=c$ and $Q(0)=b-c$. For an odd second abscissa, testing the surface equation modulo 4 gives precisely four residues $(x,y,z)$ at that mark: $(1,0,1),(1,0,3),(1,2,1),(1,2,3)$. Each yields the same marked system modulo 2. Their constants are tested separately modulo 4.

For every nonzero coefficient $c_i$ of positive degree in the six polynomials, take $-v_2(c_i)/i$, and let $h$ be their maximum. If there are no such coefficients, or $h\le 1/2$, every denominator at index $i$ divides $2^{\lfloor i/2\rfloor}$ up to a 2-adic unit. Since $w^2/2=v^2-v-(1+v)w$, every coordinate then belongs to the original integral Pell-coordinate lattice with the same degree bound. The integral-lattice check modulo 4 forces $x$ even at every integral Pell point, contrary to the odd second abscissa. [Integral-lattice argument](QuarticGeometry.md#integral-coefficients-in-the-original-pell-coordinates-at-2) · [Integral-lattice checker](quartic_local_geometry.py)

For $h=a/e>1/2$ in lowest terms, use $w=\pi^a s$ with $\pi^e=2$. The extension is totally ramified by Eisenstein, so its residue field is $\mathbf F_2$. All six rescaled polynomials have integral coefficients. Some coefficient at a positive index is a unit by the definition of $h$, and a unit at index $i$ requires $e\mid i$. In particular $e\le6$. Reduction gives $v^2=v$ since $a>0$ and $2a-e>0$. Evaluating at $v=0,1$ gives two ordinary polynomial triples $A,B$ satisfying the surface equation over $\mathbf F_2[s]$. They have the two prescribed constant terms, their degrees are at most $4,3,6$, and the component degrees of $Q=B-A$ are strictly below these bounds. Some component of $A$ or $Q$ is nonconstant. Exhausting these small polynomial spaces gives the nonconstant split residues in the table.

| Reduced denominator $e$ | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|
| Split residues | 22 | 1 | 0 | 0 | 0 | 0 |

## Testing the first correction

Return to $\mathbf Q_2$ and express each polynomial in the normalized basis $E_i=w^i/2^{\lfloor hi\rfloor}$. Every coefficient is integral. The basis multiplication adds the exponent $\lfloor h(i+j)\rfloor-\lfloor hi\rfloor-\lfloor hj\rfloor$ of 2, which depends only on the fractional part of $h$. In $E_i E_j v^2$, the terms involving $w,wv$ have exponent at least $\lfloor h\rfloor$, and the term involving $w^2/2$ has exponent at least $\lfloor 2h\rfloor-1$. For $h\ge2$ these three terms vanish modulo 4. Thus the slopes remaining from the table need only four representatives. The following counts apply to each of the four permitted second residues.

| Slopes $h$ | Compatible normalized tuples modulo 2 | Tuples lifting modulo 4 |
|---|---:|---:|
| $1$ | 22 | 0 |
| Integers $\ge 2$ | 22 | 0 |
| $3/2$ | 256 | 0 |
| Strict half-integers $\ge 5/2$ | 256 | 0 |

For each half-integral slope, the 13 odd-index coefficients have unrestricted normalized parity before imposing the identity. The checker tries all $2^{13}=8192$ assignments. At every viable normalized tuple, the 23 correction variables consist of all positive-degree coefficients of $P,Q$ for bounds $4,3,6$. The identity has 23 nonconstant coefficient equations in the two components, of degrees at most 12 and 11. The constant equations already hold modulo 4 at the prescribed marks. The first correction uses the derivatives $3x^2,2yz,y^2+2z$ and the residual divided by 2. In characteristic two its sign is immaterial.

Python enumerates the residue classes, constructs all 2,224 correction matrices, checks their ranks, and locates one of 26 inconsistent row subsystems inside every matrix. Lean's kernel checks that all 26 recorded subsystems are inconsistent for every choice of the 23 correction digits. The balancing argument above and the enumeration-to-matrix correspondence are outside the Lean theorem. [Enumeration and matrix construction](two_point_primary_two.py) · [Lean certificate](TwoPointPrimaryTwo.lean)

Reproduce both checks from the project directory.

```sh
uv run --with python-flint==0.9.0 python two_point_primary_two.py
lake -d .. env lean TwoPointPrimaryTwo.lean
```
