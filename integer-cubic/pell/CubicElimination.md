# Excluding the six cubic lifts through $(0,1,1)$

Consider the Pell conic $u^2-3v^2=1$ and put
$
L=1-3t^2,\quad u=(1+3t^2)/L,\quad v=2t/L.
$
A polynomial of total degree at most three in $u,v$ has the form $X(t)/L^3$ with $\deg X\le 6$. Write the three coordinates as $(X,Y,Z)/L^3$. The seed fixes the constant terms of $(X,Y,Z)$ at $(0,1,1)$. The cubic surface equation becomes
\[
X^3+ZY^2+Z^2L^3=2L^9 .
\]
The remaining eighteen coefficients give eighteen equations in eighteen unknowns.

**Conclusion.** No rational solution of this coefficient system, with coefficients integral at 7 and $\gcd(\bar X,\bar L)=1$ modulo 7, has the prescribed seed. The coprimality condition on $\bar X$ means it retains its poles at the two roots of $L$. The argument uses exact finite-field computations, Hensel's lemma and an integer resultant.

There is also a restriction valid for every nonsplit Pell discriminant. If $x$ has pole order three, $y$ must also have pole order three, and the pole orders of $z$ and $z+y^2$ are three and six in some order. Indeed their orders are multiples of three adding to nine. The larger order equals the pole order of their difference $y^2$, so it must be even. Thus a search in which all three coordinates have degree at most three can take $z$ to have pole order three and $z+y^2$ to have pole order six. [Lean proof of the pole orders](PoleOne.lean)

## A nine-variable system with the same six lifts

For a scalar $b$ define
\[
s=\frac{t+bt^2}{L},\qquad r=\frac{1+2bt+3t^2}{L},
\qquad r^2=1+4bs+12s^2.
\]
Choose cubics $C(s),J(s)$ and a quadratic $E(s)$, with
$C(0)=0$, $J(0)=E(0)=1$. Set $x=C(s), z=J(s), y=rE(s)$. The condition
\[
C^3+J^2+(1+4bs+12s^2)E^2J=2
\]
has nine nonconstant coefficients. Its Jacobian uses columns in the order $b$, the three nonconstant coefficients of $C$, the three of $J$, and the two of $E$.

An exhaustive enumeration over $\mathbb F_7$ gives exactly six solutions of the eighteen-variable system with $\gcd(\bar X,\bar L)=1$. All six occur in the nine-variable system. The derivative $X'(0)$ distinguishes the six records. The last two columns will be used to normalize their cubic root fields.

| $X'(0)$ | $b$ | Reduced Jacobian determinant | $w$ | $a$ |
|---|---|---|---|---|
| 1 | 5 | 5 | 1 | 0 |
| 2 | 5 | 5 | 4 | 0 |
| 3 | 2 | 2 | 2 | 0 |
| 4 | 5 | 5 | 2 | 0 |
| 5 | 2 | 2 | 4 | 0 |
| 6 | 2 | 2 | 1 | 0 |

For example, the first row has $C=s+4s^2+3s^3$, $J=1+5s+6s^3$, and $E=1+5s^2$. Each reduced Jacobian and each full Jacobian is invertible modulo 7. Multivariate Hensel lifting therefore gives a unique solution in each residue class for each system over $\mathbb Z_7$. Substitution into the full system sends the reduced lift to a full lift in the same class, so uniqueness identifies them. Every rational solution in any of these six classes consequently admits this nine-variable representation over $\mathbb Q_7$. [Enumeration and full Jacobians](search_pell_mod.py) · [Reduced models and Jacobians](cubic_elimination_symmetry.py)

For rational $X,Y,Z$, the representation descends to $\mathbb Q$. In each row the helper verifies
\[
\gcd\big(C(s)/s,(J(s)-1)/s\big)=1 \pmod 7.
\]
Both leading coefficients are units, so their resultant is nonzero in $\mathbb Q_7$. Also $t+bt^2$ and $L$ are coprime because $b^2\ne3\pmod7$. It follows by substitution and clearing denominators that the monic gcd of $X(t)$ and $Z(t)-L^3$ is the monic associate of $t(1+bt)$. Computing that monic gcd over $\mathbb Q$ gives the same polynomial. Thus $b\in\mathbb Q$. Since $s=t+O(t^2)$ and $r=1+O(t)$ at the seed, successive Taylor coefficients recover $C,J,E$ over $\mathbb Q$.

## Two rational parameters for the cubic divisor

At every root $\theta$ of $J$, the surface identity gives $C(\theta)^3=2$. Since $J$ is cubic and $T^3-2$ is irreducible, $J$ is irreducible and
\[
\mathbb Q(\theta)=\mathbb Q(C(\theta))=\mathbb Q(\alpha),\qquad \alpha^3=2.
\]
Use the identification $C(\theta)=\alpha$ and write $\theta=c+i\alpha+j\alpha^2$. The leading coefficient of $J$ is a 7-adic unit, so $\theta$ is integral at 7. The basis $1,\alpha,\alpha^2$ has discriminant $-108$, a 7-adic unit, hence $c,i,j$ are integral at 7. In $\mathbb F_7[\alpha]/(\alpha^3-2)$, solve $J(\theta)=0$, $C(\theta)=\alpha$. Each row gives $c=0$ and $i\ne0$. The change $s'=(s-c)/i$ therefore takes the root to $\alpha+w\alpha^2$ and the seed to $a$, where $w=j/i$ and $a=-c/i$. Their residues are recorded above.

The cube-root symmetries disappear after setting $W=w^3$, $S=w s'$, and $B=wa$. Every row satisfies $(W,B)\equiv(1,0)\pmod7$. Define
\[
P(S)=S^3-6WS-2W-4W^2,\quad G(S)=S-S^2+4W,\quad k=W(1-2W)^3,
\qquad A=P(B),\ H=G(B).
\]
At the transformed root $S=w(\alpha+w\alpha^2)$, one has $P(S)=0$ and $G(S)=w(1-2W)\alpha$. The cubic $z$ is therefore $P(S)/A$ by its value at the seed. The polynomial $x-G(S)/(w(1-2W))$ is a multiple of $P$ of degree at most three. Evaluating at $S=B$ fixes the multiple and gives
\[
z=\frac{P(S)}{A},\qquad x=\frac{A G(S)-H P(S)}{w(1-2W)A}.
\]
All denominators are nonzero modulo 7. Put $Q(S)=(2k-G(S)^3)/P(S)$, which is a polynomial by the cubic-root identity. Then $kA^2 y^2=F(S)$, where
\[
F=A^3 Q+3 A^2 H G^2-3 A H^2 G P+H^3 P^2-A k P .
\]
This is an exact polynomial identity after multiplication by $P$.

## The discriminant obstruction

For a rational lift, $F(S)$ is a nonzero scalar times a quadratic times the square of a quadratic, by the nine-variable representation and the invertible affine change from $s$ to $S$. Its degree is six and its leading coefficient is $H^3\ne0$. The factor $E$ has degree two in all six rows. Therefore $F$ and $\partial_S F$ have a common divisor of degree at least two, including the case where $E$ itself has a double root.

Let $R(W,B)=\operatorname{disc}_S(F)$. At the putative pair $(W,B)$, the Sylvester matrix of $F,\partial_S F$ has corank at least two by the common divisor just found. Both the determinant and all its first cofactors vanish. Differentiating its determinant with respect to $B$ now gives zero. Because the leading coefficient of $F$ is nonzero here, the relation between the resultant and discriminant yields
\[
R(W,B)=\partial_B R(W,B)=0.
\]

Exact factorization gives, up to a nonzero rational constant,
\[
R=W^4 H^6 A^6 (2W-1)^8\,\Delta(W,B),
\qquad \deg_W\Delta=28,\quad \deg_B\Delta=42.
\]
The displayed elementary factors are nonzero at every pair reducing to $(1,0)$. Hence $\Delta(W,B)=\partial_B\Delta(W,B)=0$. Its leading coefficient in $B$ is the constant 4. Consequently $W$ is a zero of $\operatorname{disc}_B(\Delta)$, an integer polynomial of degree 1148. Its factor degrees and multiplicities are
\[
W^{195}(2W-1)^{660} P_{37}(W)P_{62}(W)^2P_{44}(W)^3,
\]
up to a nonzero constant, where the subscripts give the degrees. For the factors of degrees 37 and 62, reduction modulo 5 has nonzero leading coefficient and no root. For degree 44 the same holds modulo 13. A rational root in lowest terms would therefore give an impossible projective root in the corresponding finite field. Thus the only rational possibilities are $W=0$ and $W=1/2$. Their residues modulo 7 are 0 and 4, whereas each of the six branches requires $W\equiv1\pmod7$. [Exact discriminant and projection](cubic_elimination.py) · [Lean rational-root certificate](CubicEliminant.lean)

## The other seed $(−2,3,1)$

For the same Pell conic and full-pole condition, reduction modulo 7 also gives six candidate triples through $(−2,3,1)$. Each already fails to lift modulo 49. To see this, choose integral polynomial representatives of each triple with their constant terms equal to $-2,3,1$ exactly. Compute the eighteen nonconstant coefficients of the residual
\[
T=X^3+ZY^2+Z^2L^3-2L^9.
\]
The constant coefficient vanishes exactly and the remaining coefficients are divisible by 7. To lift, the eighteen correction digits must solve $Jv=-T/7\pmod7$, where the Jacobian columns are $3X^2t^j$, $2ZYt^j$, and $(Y^2+2ZL^3)t^j$ for $1\le j\le6$. On every branch, $J$ has rank 16 and the augmented matrix has rank 17. For each of the six systems Lean verifies a vector that annihilates the columns of $J$ but pairs nontrivially with the right-hand side. This excludes every rational model with 7-integral coefficients and full poles modulo 7 through this seed. [Lift and rank checks](cubic_elimination_symmetry.py) · [Lean obstruction](CubicLiftObstruction.lean)

## A uniform obstruction for reflection-symmetric cubics

The two-parameter elimination also gives a conclusion over $\mathbb Q$ for arbitrary Pell discriminant. Suppose a model through $(0,1,1)$ has a rational quotient coordinate $s$ such that
\[
 x=C(s),\qquad z=J(s),\qquad y^2=R(s)E(s)^2,
\]
where $C,J\in\mathbb Q[s]$ are cubic, $R,E\in\mathbb Q[s]$, $\deg R\le2$, and the seed occurs at a rational value of $s$. Then the model cannot satisfy the surface equation identically. This covers any quadratic cover $r^2=R(s)$ on which $x,z$ are cubic in $s$ and $y=rE(s)$, regardless of the square class of the leading coefficient of $R$. The reflection on that cover sends $r$ to $-r$. The earlier modulo-7 argument establishes that every one of the six specified branches for $D=3$ would have this symmetry.

Indeed, $J\mid 2-C^3$, so a root $\theta$ of $J$ generates $\mathbb Q(\sqrt[3]{2})$, as above. The polynomial $(2-C^3)/J-J$ has degree six, because $C$ and $J$ have degree three. As it equals $R E^2$, one has $\deg E\ge2$. Its discriminant must therefore vanish with the Sylvester corank condition used above.

Write $\alpha=\sqrt[3]{2}$ and $\theta=c+i\alpha+j\alpha^2$. At least one of $i,j$ is nonzero. If both are nonzero, translate and scale $s$ so the root has the form $\alpha+w\alpha^2$ with $w=j/i\ne0$. The same pair $(W,B)$ is now available entirely over $\mathbb Q$. The factor $A=P(B)$ is nonzero because the rational seed cannot be a root of the irreducible cubic $J$. Also $H=G(B)\ne0$, since $H=0$ in the formula for $x$ would give $\deg x\le2$. Thus $W\ne0$ and $2W-1\ne0$, the latter because the rational cube $w^3$ cannot be $1/2$ (the exponent of 2 in a rational cube is divisible by three). All factors divided out of the sextic discriminant are consequently nonzero. The projected discriminant permits only $W=0$ or $W=1/2$, which excludes this case.

If exactly one of $i,j$ is nonzero, normalize the root to $\alpha^e$ for $e=1$ or $2$. Use the quotient variable $s$ after this change and denote the transformed rational seed by $a$. Put
\[
 P=s^3-2^e,\quad A=a^3-2^e,\quad H=s^e,\quad B=a^e.
\]
At the normalized root, $H/e=\alpha$. The same interpolation yields
\[
 z=P/A,\qquad x=(AH-BP)/(eA).
\]
Writing $Q=(2e^3-H^3)/P$, the sextic $e^3A^2 y^2$ becomes
\[
 F=A^3Q+3A^2BH^2-3AB^2HP+B^3P^2-e^3AP .
\]
Exact factorization of $\operatorname{disc}_s F$ gives the following degrees and multiplicities. For every nonlinear factor, the indicated prime gives a reduction of the same degree with no finite-field root, excluding a rational root.

| Normalized root | Factor vanishing at $a=0$ | Other factor degrees (multiplicity, test prime) |
|---|---|---|
| $\alpha$ | $a^6$ | $3\ (6,7)$, $24\ (1,5)$ |
| $\alpha^2$ | $a^{12}$ | $3\ (6,7)$, $9\ (1,5)$, $33\ (1,5)$ |

The only possible rational discriminant root is $a=0$, which gives $B=0$ and $x=H/e$ of degree at most two. This excludes both exceptional normalizations and finishes the uniform obstruction. [Exact factorization and residue tests](cubic_elimination_symmetry.py)

## Reproduce the computations

```sh
uv run --with python-flint==0.9.0 cubic_elimination_symmetry.py
uv run --with python-flint==0.9.0 cubic_elimination.py
lake -d .. build CubicEliminant CubicLiftObstruction
```

The first script enumerates both seeds and checks the Jacobians and exceptional normalizations. The second recomputes the two discriminants over the integers, multiplies the factors back together, and checks their coefficients against the Lean input. Lean verifies that the resulting polynomial has exactly the two stated rational roots and excludes the required residue class modulo 7. The passage from a candidate substitution to a root of that polynomial uses the lifting and descent arguments above.
