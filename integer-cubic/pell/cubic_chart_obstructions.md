# Positive-slope cubic charts at 7 for D = 3

For the degree-six numerators of a cubic Pell substitution through either seed, the finite calculation excludes balancing slopes 1, 2 and 3. At $h\ge 4$, five of seven normalized residue classes are excluded uniformly. The uniform argument at a second radius also excludes the final two classes. The finite calculation uses exact modular polynomial arithmetic in Python and FLINT. [Uniform cubic obstruction](CubicAnnulus.md)

## Coordinates and chart normalization

Write $Q=1-Ct^2$ and let $X,Y,Z$ have degree at most six and constants $(0,1,1)$ or $(-2,3,1)$. The equations are the 18 nonconstant coefficients of
$$
F=X^3+ZY^2+Z^2Q^3-2Q^9=0.
$$

The positive balancing slope $h$ records the rescaling $t\mapsto7^h t$ required to make all coefficients integral with some nonconstant coefficient a unit. If $h=a/b$ in lowest terms, every exponent of a surviving nonconstant coefficient is divisible by $b$. The exhaustive residue search finds that the gcd of the surviving exponents is 1 in each class, so $h$ is integral. The original local balancing and the six residue classes already excluded modulo 343 are checked in [seeded_denominator_lifts.py](seeded_denominator_lifts.py).

Before the final normalization, the denominator coefficient is $3\cdot7^{2h}$. At the first seed take $g=X_4/Y_3$, which is a unit. At the second seed take $g=X_1$ if its residue is nonzero and $g=Y_1$ otherwise. Substitute $t/g$ for $t$. This sets $X_4=Y_3$ or fixes the selected linear coefficient to 1 and gives $C=3\cdot7^{2h}/g^2$. Thus $C=7^{2h}c$ with $c\bmod7\in\{3,5,6\}$. Every higher digit of $c$ is allowed by the local squareclass, since each nonzero square mod 7 lifts to a square in $\mathbb Z_7^\times$. Counting arbitrary such units is also valid for rational substitutions.

There are 19 unknowns in the order $X_1,\dots,X_6,Y_1,\dots,Y_6,Z_1,\dots,Z_6,C$. The first 15 coefficient equations and the normalization condition have a 16-by-16 Jacobian minor invertible modulo 7 on each chart. Write $U,V$ for the deviations of the two indicated free $Z$-coefficients from their least nonnegative residues. Together with $C$, these give three free variables. A constant unit minor yields unique power series in $\mathbb Z_7[[U,V,C]]$ for the other 16 coefficients in their prescribed residue classes. Substitution gives three obstructions $\Phi_i=[t^i]F$ for $i=16,17,18$.

## Ordinary initial forms

In the table set $U=7u,V=7v,C=7c$. The displayed forms are $7^{-d_i}\Phi_i(7u,7v,7c)\bmod 7$ as **polynomials**, for the exact orders $d_i$. In the associated graded ring of $(7,U,V,C)$ these are dehomogenized at the symbol of 7 equal to 1. Rehomogenizing to degree $d_i$ recovers the full homogeneous term including powers of that symbol. Every coefficient in the table is in $\mathbb F_7$. Each six-digit string gives consecutive coefficients $X_1,\ldots,X_6$ and the seed fixes $X_0$.

| Chart | Seed | $X_1\ldots X_6$ | Free $Z$ indices | $L$ | Orders | $\Phi_{16}$ initial | $\Phi_{17}$ initial | $\Phi_{18}$ initial |
|---|---|---|---|---|---|---|---|---|
| 0 | $(0,1,1)$ | 000300 | 4,5 | | 2,4,3 | $4c^2$ | $6c^2(u+4vc+c^2)$ | $4c^3$ |
| 1 | $(-2,3,1)$ | 035500 | 5,6 | $u-v$ | 2,3,3 | $c(L-c)$ | $2(L+3c)(L+5c)^2$ | $L^3+6L^2c+5Lc^2+6c^3$ |
| 2 | $(-2,3,1)$ | 125300 | 4,6 | $u+3v+5$ | 2,3,3 | $4c(L-c)$ | $L(L+4c)^2$ | $L^3+L^2c+5Lc^2+4c^3$ |
| 3 | $(-2,3,1)$ | 131600 | 5,6 | $u+v+6$ | 2,3,3 | $6c(L+c)$ | $2L^3+2L^2c+2L^2+5Lc^2+3Lc+4c^3+2c^2$ | $6L^3+6L^2c+2Lc^2+6c^3$ |
| 4 | $(-2,3,1)$ | 134200 | 5,6 | | 2,3,3 | $5c^2$ | $5c^3$ | $5c^3$ |
| 5 | $(-2,3,1)$ | 160000 | 5,6 | $u+2v+3$ | 2,3,3 | $3c^2$ | $4L^3+4c^3$ | $6L^3+3c^3$ |
| 6 | $(-2,3,1)$ | 162200 | 5,6 | | 2,3,3 | $5c^2$ | $6c^3$ | $5c^3$ |

## Certificate at positive even denominator valuation

For each column below set $(U,V,C)=(7u,7v,7^w c)$ with $w=2,4,6,8$ respectively. Retain all $c\in\mathbb Z_7$ with its first digit in $\{3,5,6\}$ for the three fixed slopes. For $w=8$ allow every $c\in\mathbb Z_7$, including zero, so a single empty search covers all $h\ge4$. A table entry gives the number of digit levels until all residue boxes are excluded.

| Chart | $h=1$, mod $7^{12}$ | $h=2$, mod $7^{15}$ | $h=3$, mod $7^{20}$ | all $h\ge4$, mod $7^{22}$ |
|---|---:|---:|---:|---:|
| 0 | 1 | 3 | 5 | unresolved by this test |
| 1 | 2 | 4 | 6 | 6 |
| 2 | 2 | 4 | 4 | 4 |
| 3 | 2 | 2 | 2 | 2 |
| 4 | 1 | 3 | 5 | unresolved by this test |
| 5 | 1 | 4 | 4 | 4 |
| 6 | 1 | 3 | 3 | 3 |

The checker computes the full polynomial jets modulo the indicated powers of 7. Starting from the residue representatives, it repeatedly subtracts a fixed lift of the inverse Jacobian applied to the 16 selected equations. If the equations vanish modulo $7^n$, their Taylor expansions after the correction vanish modulo $7^{n+1}$, since the correction is divisible by $7^n$ and the Jacobian times the chosen inverse is the identity modulo 7. This holds coefficientwise over $(\mathbb Z/7^N)[u,v,c]$. The checker verifies divisibility after every iteration and checks the 16 final equations as polynomial identities. It also verifies that independently computed jets agree on substituting $c\mapsto7^{w'-w}c$ and reducing to their common precision.

For each of the three remaining polynomials, divide out the highest common power of 7 visible at that precision and reduce modulo 7. If the whole polynomial vanishes at that precision it imposes no digit condition. Enumerate all triples in $\mathbb F_7^3$ satisfying the three resulting necessary conditions and the current restriction on $c\bmod7$. For each surviving pair $(a,b)$, substitute $u=a+7u',v=b+7v'$ in the original three jets and recurse, retaining all permissible denominator units. This retains all higher denominator digits symbolically, even when only its initial digit has been specified. Empty lists certify impossibility already at the given modulus.

The code prints every level count. For example, on chart 1 with $h\ge4$ the counts of viable $(u\bmod7^j,v\bmod7^j,c\bmod7)$ after the successive necessary tests are $49,343,2401,2401,16807,0$. On chart 4 with $h=3$ they are $18,126,294,2058,0$. The ordinary initial forms in the first table are checked coefficientwise against independently encoded expressions. The command also prints all 21 weighted initial polynomials for $w=2$.

```bash
uv run --with python-flint==0.9.0 cubic_chart_obstructions.py --forms
```

The positive-slope cases left by this finite test have $h\ge4$, with either the first seed and $X\equiv3t^4\pmod7$, or the second seed and $X\equiv-2+t+3t^2+4t^3+2t^4\pmod7$, in the stated normalization. The second-radius argument excludes both cases at every slope. [Uniform cubic obstruction](CubicAnnulus.md)
