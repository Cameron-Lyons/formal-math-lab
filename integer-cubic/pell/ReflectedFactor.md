# Reflections fixing the abscissa and last coordinate

Consider a rational substitution through $(x,y,z)=(0,1,1)$ with $x=X(s)$, $z=Z(s)$ and $y=rE(s)$, where $r^2=Q(s)$. The degrees of $X,E,Z$ are at most $4,2,6$, respectively, and their constant terms are $0,1,1$. The second marked point is free. The required polynomial identity is

$$Z(Z+QE^2)=2-X^3.$$

Write $Q=1+As+Cs^2$. The computation below rules out $A=0$ in characteristic zero. For $A\ne0$ change the parameter to $As$ and write $Q=1+s+ks^2$. For the original Pell conic the normalized $k$ is $3B^2$ for a nonzero rational $B$. More generally any positive nonsquare rational $k$ gives a Pell conic. Namely if $u^2-kv^2=1$, then $s=(u+2kv-1)/(2k)$ and $r=u+v/2$ satisfy the quadratic and send $(1,0)$ to $(0,1)$. Lean verifies this formula and that each reflected-factor identity gives the desired cubic identity. [Lean theorems](ReflectedOrdinate.lean)

For $h(a/b)=\max(|a|,b)$ in lowest terms, the six finite-field computations give the following exclusions, allowing arbitrary rational coefficients in $X,E,Z$.

* Every positive nonsquare $k$ with $h(k)\le30$ is excluded. The first parameter by height passing the six congruences is $31$.
* For $k=3B^2$, every $B\ne0$ with $h(B)\le18$ is excluded. The first positive $B$ passing is $19/2$.

Lifting the surviving parameters gives two further bounds. For all positive rational $k$ of height at most $1000$, and separately for all $k=3B^2$ with $h(B)\le1000$, there is no nonconstant identity when each of the twelve coefficients of $X,E,Z$ has height at most $10^{60}$. These are computational results in the specified reflection family. [Exact enumeration and lifting](reflected_factor.py)

## Denominators and the modular enumeration

If $X$ is constant, $X=0$ and both factors of $2$ are constant, so $Z=1$ and $QE^2=1$. Thus any nonconstant substitution on a nonconstant quadratic has nonconstant $X$.

At a prime $p$ in the table, take $h=\max_{i>0,X_i\ne0}-v_p(X_i)/i$. Set $s=\lambda T$ in a totally ramified extension of $\mathbb Q_p$ with $v_p(\lambda)=h$. The residue field remains $\mathbb F_p$ and $X(\lambda T)$ is integral with nonconstant reduction. The constants of the two factors of $2-X^3$ are $1,2$. Each factor therefore has minimum coefficient valuation at most zero. Those minima add under multiplication and the product is integral, so both factors are integral. Their difference $QE^2$ is then integral. Applying the same argument to $Q$ and $E$, both with unit constant, shows that $Q(\lambda T)$ and $E(\lambda T)$ are integral. In the $3B^2$ case the reduced quadratic coefficient still has the form $3b^2$, since $B\lambda$ is integral.

The program enumerates all nonconstant $X$ over $\mathbb F_p$ up to $T\mapsto cT$ for $c\ne0$. It enumerates each degree-at-most-six divisor $Z$ of $2-X^3$ with $Z(0)=1$, requiring that the complementary factor also have degree at most six. To split their difference as $QE^2$, first take the squarefree part of odd multiplicities as $Q$. A second possibility occurs when this part is constant and a squared linear factor can be moved from $E^2$ into $Q$. The degree bounds on $Q,E$ make this list exhaustive. The two normalizations of the factors use $Q(0)=E(0)=1$.

At each of the six primes all resulting quadratics have nonzero linear coefficient. This excludes $A=0$. For normalized $Q=1+s+ks^2$ its rescaled linear coefficient is $\lambda$. Thus $v_p(\lambda)=0$, the original chart has integral coefficients at $p$, and its reduction can be read among the records normalized to linear coefficient one. In particular none of the sieves assumes good reduction for the input. The independent characteristic-seven check enumerates $X,E,Q$ directly and tests whether $Q^2E^4+8-4X^3$ is a square.

| Prime | Positive $k$ of height $\le1000$ surviving cumulatively | Positive $B$ of height $\le1000$ surviving cumulatively |
|---:|---:|---:|
| 7 | 228387 | 304501 |
| 13 | 65136 | 130501 |
| 19 | 25931 | 45623 |
| 37 | 12193 | 16724 |
| 67 | 4176 | 5637 |
| 79 | 891 | 980 |

## Exact lifts

At $79$ there are $66$ normalized residue records with arbitrary quadratic coefficient and $33$ in squareclass $3$. At each record the twelve nonconstant coefficient equations of $X^3+Z^2+QE^2Z=2$ have nonsingular Jacobian with respect to the twelve coefficients of $X,E,Z$ at fixed $k$. Its columns are the appropriate shifts of $3X^2$, $2QEZ$, and $2Z+QE^2$.

For each surviving rational parameter, the checker lifts every corresponding residue by this invertible matrix. At modulus $79^m>2(10^{60})^2$, rational reconstruction tests every coefficient against the height bound. There were $3474$ lifts for the $891$ values of $k$ and $4581$ lifts for the $980$ values of $B$. No exact identity survived. The reduction, linear solves and reconstruction use exact arithmetic. The finite enumerations are implemented in Python with FLINT.

```sh
uv run --with python-flint==0.9.0 python reflected_factor.py --check-seven
uv run --with python-flint==0.9.0 python reflected_factor.py --general --parameter-height 1000
uv run --with python-flint==0.9.0 python reflected_factor.py --parameter-height 1000
lake -d .. env lean ReflectedOrdinate.lean
```
