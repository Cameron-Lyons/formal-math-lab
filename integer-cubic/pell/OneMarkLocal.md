# A quartic Pell substitution through one marked point

The mark is $(x,y,z)=(0,1,1)$ at $(u,v)=(1,0)$ on $u^2-3v^2=1$. The degree bounds are $4,3,6$. The unrestricted mixed quartic remains unresolved over $\mathbb Q_3$ and over $\mathbb Q$ in the calculations below.

## A substitution over the 2-adic field

Over any characteristic-zero field set
$$
Y(s)=(108s^3-239)/13,\quad X(s)=2s(Y(s)-1)/3,\quad
Z(s)=(44-Y(s)^2-16Y(s))/27.
$$
These polynomials satisfy the cubic identity. Hensel's lemma supplies $a\in\mathbb Z_2$ with $3a^3=7$, since $3s^3-7$ is even at 1 and its derivative is odd there. Taking $s=a+v$ gives the prescribed mark and $X(a+1)\ne0$. Lean proves the identity, the root existence and the second abscissa assertion. [Lean proof](OneMarkLocalTwo.lean)

## Two restricted classes over the 3-adic field

There is no nonconstant ordinary polynomial triple of degrees at most $4,3,6$ over $\mathbb Q_3$ taking the seed at zero. For each nonzero coefficient $c_i$ of positive index take $-v_3(c_i)/i$ and let $h$ be the maximum. Rescale the variable by an element of valuation $h$ in a totally ramified extension. The reductions are integral, at least one is nonconstant, and every surviving index is divisible by the denominator of $h$. If $X$ reduces to zero, $Z(Z+Y^2)=2$ forces $Y,Z$ constant, so $X$ has nonconstant reduction. The 26 possible reduced triples have only two cases supported on even indices and none supported on multiples of any denominator from 3 to 6. A larger denominator cannot occur. For integral $h$, 24 classes fail modulo 9. Each of the other two has 177,147 lifts modulo 81 and all fail modulo 243. For half-integral $h$, rescale first by the integer part. The coefficient lattice then has basis $t^i/3^{\lfloor i/2\rfloor}$. Checking the odd-index coefficients in this basis leaves 18 classes modulo 3. Their correction matrices all have rank 9 and augmented rank 10. This also excludes seeded triples of the form $X(\ell),Y(\ell),Z(\ell)$ for a nonconstant linear Pell function $\ell$ and ordinary polynomials of the stated degrees, by translating $\ell$ to zero at the mark. [Finite checker](local_quartic_three.py)

The second exclusion concerns $x=A(y-1)^2+B(y-1)$ with $A\ne0$. Put $s=y-1$. The double cover
$$
w^2=F(s)=(1+s)^4+8-4(As^2+Bs)^3
$$
must have a component parametrized by the Pell conic, so the part of $F$ left after removing all square factors has degree at most two. Since $F$ has degree six, $\gcd(F,F')$ has degree at least two. The Sylvester matrix for $F,F'$ has corank at least two. Its determinant and the derivative of that determinant in $B$ vanish, because every cofactor vanishes. Write $\operatorname{disc}_s(F)=cA^3D(A,B)$. Hence $D=D_B=0$. The leading coefficient of $D$ in $B$ is $59049A$. Up to a constant and a power of $A$, $\operatorname{disc}_B(D)$ factors into powers of polynomials of degrees 6, 24 and 48. Their Newton polygons force a 3-adic root to be a unit. The three factors have no unit root modulo 9, 3 and 81 respectively. [Discriminant and valuation checker](local_quartic_three.py)

## Integral numerator chart

Put $L=1-3t^2$. The original coordinates are $X/L^4,Y/L^3,Z/L^6$. The numerators in $\mathbb Z_3[t]$ have degree bounds $8,6,12$, constant terms $0,1,1$ and identity $X^3+Z(Y^2+Z)=2L^{12}$. The census counts residue triples modulo 3 admitting at least one lift to each modulus.

| Modulus | All surviving residues | Nonconstant reduced $X$ |
| --- | ---: | ---: |
| 3 | 759 | 758 |
| 9 | 21 | 20 |
| 27 | 19 | 18 |
| 81 | 17 | 16 |

The constant residue lifts exactly using numerators $0,L^3,L^6$. In the other classes, first solve the linear system for $Y,Z$ modulo 9. Next correct $X$ by $3^k$ and $Y,Z$ by $3^{k+1}$ for $k\ge1$. The coefficient equation at order $3^{k+1}$ is linear with columns $X^2t^i,2YZt^i,(Y^2+2Z)t^i$ modulo 3. The leading coefficients $a=X_8,b=Y_6,c=Z_{12}$ all vanish modulo 3 in the 21 possible residues. The degree-24 equation gives $a^3+b^2c+c^2=0\bmod81$, forcing $a=c=0\bmod9$. This rules out the two additional classes lost between 27 and 81. The checker verifies explicit lifts in each surviving class by coefficient multiplication. Lean certifies the leading-coefficient implication on integer representatives. [Lifting checker](quartic_one_mark_three_lifts.py) · [Lean lemma](OneMarkLocalThree.lean)

## Integral coefficients in the Pell ring

Write $P(v)+uQ(v)$ for a function of degree at most $d$, with $\deg P\le d,\deg Q<d$ and $P,Q\in\mathbb Z_3[v]$. The pair $f_\pm=P\pm Q$ has equal coefficients in degree $d$. Every pair with this property arises since 2 is invertible. Modulo 3 the ring splits into the components $u=+1,-1$, with the mark on the first component. The full multiplication rule is
$$
(fg)_\pm=f_\pm g_\pm+(3/4)v^2(f_+-f_-)(g_+-g_-).
$$
Enumerating $Y,Z$ and reconstructing the unique polynomial cube root for $X$ gives 27 marked and 387 unmarked component triples over $\mathbb F_3[v]$. Matching their three top coefficients gives 1,161 pairs. Of these, 56 lift modulo 9.

| Marked component modulo 3 | Pairs lifting to 9 |
| --- | ---: |
| $(0,1,1)$ | 20 |
| $(-v^2,1,1+v^3)$ | 18 |
| $(-v^2,1,1-v^3)$ | 18 |

Of the 36 pairs with nonconstant marked component, exactly 28 lift to modulus 27 and all 28 lift to modulus 81. The checker verifies the complete polynomial identity modulo 81 for each surviving pair. For the 20 pairs with constant marked component this census stops at modulus 9. A nonconstant 3-adic function can have constant reduction. [Lifting checker](quartic_one_mark_three_lifts.py)
