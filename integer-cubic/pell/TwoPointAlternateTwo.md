# The alternate two-point quartic Pell substitution at 2

Suppose coordinates of degrees at most $(4,3,6)$ on $u^2-3v^2=1$ satisfy $x^3+y^2z+z^2=2$ and take the values $(0,1,1)$ and $(-2,3,1)$ at $(1,0)$ and $(2,1)$. Every such rational substitution belongs to the original 2-integral Pell-coordinate lattice. The separate integral-lattice obstruction therefore excludes this pair of marks. [Integral-lattice Lean proof](two_point_alternate_two.lean)

Use $w=u-1-v$, $v^2=(1+w)v+w+w^2/2$, and coordinates $P(w)+vQ(w)$ of degrees $(d,d-1)$ as in the primary two-point argument. The pairs $(P(0),Q(0))$ are now $(0,-2),(1,2),(1,0)$. For nonconstant coefficients $c_i$ let $h=\max(-v_2(c_i)/i)$. If no such coefficients exist or $h\le1/2$, integrality in the original lattice follows from $w^2/2=v^2-v-(1+v)w$. [Normalization and split reduction](TwoPointPrimaryTwo.md)

For $h=a/e>1/2$ in lowest terms, both components of the split reduction are ordinary characteristic-two polynomial triples through $(0,1,1)$. Some nonconstant coefficient survives, and surviving indices are multiples of $e$. Jointly imposing the degree bounds on $P$ and $Q$ gives the following complete counts.

| Reduced denominator $e$ | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---:|---:|---:|---:|---:|---:|
| Nonconstant split residues | 33 | 3 | 1 | 0 | 0 | 0 |

The sole split residue for $e=3$ is $P=(0,1+s^3,1+s^6)$, $Q=(0,0,0)$. In the normalized basis $E_i=w^i/2^{\lfloor hi\rfloor}$ the checker enumerates the binary digits of every coefficient with $1\le i\le d$ for $P$ and $1\le i<d$ for $Q$. It then checks the 23 first-correction equations. The exceptional four parity tuples yield 1,024 solutions modulo 4 each. For every one of these, the next correction uses the same binary Jacobian and the residual divided by 4.

| Representative slopes | Normalized tuples modulo 2 per slope | Tuples modulo 4 per slope | Tuples modulo 8 |
|---|---:|---:|---:|
| $1,2$ | 33 | 0 | 0 |
| $3/2,5/2$ | 384 | 0 | 0 |
| $4/3,7/3$ | 512 | 0 | 0 |
| $2/3,5/3,8/3,11/3$ | 512 | 4,096 | 0 |

Modulo $2^N$, the extra $w,wv,w^2/2$ terms in the multiplication rule for $v^2$ vanish once $h\ge N$ for $N=2,3$. At these slopes the remaining rule depends only on the fractional part of $h$. The tests that already fail modulo 4 therefore stabilize at $h\ge2$. For fractional part $2/3$, the test modulo 8 stabilizes at $h\ge3$. The representatives in the table cover every slope.

Python enumerates the inputs, constructs the matrices, and locates one of 37 certified inconsistent subsystems in every terminal matrix. Whenever a first correction is consistent, it enumerates the full affine space of solutions by binary elimination. Lean’s kernel proves the inconsistency of the 37 subsystems for arbitrary choices of all 23 correction digits. The balancing argument and the correspondence between the enumeration and the finite certificates are outside this Lean theorem. [Arithmetic checker](two_point_alternate_balanced_two.py) · [Lean certificate](TwoPointAlternateTwo.lean)

Reproduce the finite checks after building the Lean project.

    uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
    lake -d .. env lean TwoPointAlternateTwo.lean
