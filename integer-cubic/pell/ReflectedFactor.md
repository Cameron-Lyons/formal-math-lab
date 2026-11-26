# Reflections fixing the abscissa and last coordinate

Consider a rational substitution through $(0, 1, 1)$ of the form $x = X(s)$, $z = Z(s)$, and $y = r E(s)$ where $r^2 = Q(s)$. Here $\deg X \le 4$, $\deg E \le 2$, $\deg Z \le 6$, the constant terms are $(0, 1, 1)$, and the second marked point is free. The cubic surface equation becomes

$$
Z(Z + Q E^2) = 2 - X^3.
$$

Write $Q = 1 + As + Cs^2$. The modular check below rules out $A = 0$ in characteristic zero. For $A \ne 0$, scaling $s \mapsto As$ normalizes $Q = 1 + s + ks^2$. On $u^2 - 3v^2 = 1$, this gives $k = 3B^2$ for some nonzero rational $B$. More generally, any positive nonsquare rational $k$ corresponds to a Pell conic $u^2 - kv^2 = 1$: setting $s = (u + 2kv - 1)/(2k)$ and $r = u + v/2$ satisfies $r^2 = 1 + s + ks^2$ and maps $(1, 0)$ to $(0, 1)$. Lean verifies this parametrization and checks that every reflected-factor identity solves the cubic equation in [ReflectedOrdinate.lean](ReflectedOrdinate.lean).

Writing $h(a/b) = \max(|a|, b)$ in lowest terms, six finite-field sieves in [reflected_factor.py](reflected_factor.py) rule out the following parameters for arbitrary rational coefficients in $X, E, Z$:

* Every positive nonsquare $k$ with $h(k) \le 30$ (the first passing parameter by height is $31$).
* Every $k = 3B^2$ with $B \ne 0$ and $h(B) \le 18$ (the first positive passing $B$ is $19/2$).

Lifting all surviving parameters modulo $79^m$ gives two bounded exclusions in this reflection family: across all positive rational $k$ with $h(k) \le 1000$, and separately across all $k = 3B^2$ with $h(B) \le 1000$, there is no nonconstant identity in which all 12 nonconstant coefficients of $X, E, Z$ have height at most $10^{60}$.

## Denominators and the modular enumeration

If $X$ is constant, then $X = 0$, so both factors of $Z(Z + QE^2) = 2$ are constant, forcing $Z = 1$ and $QE^2 = 1$. Thus any nonconstant substitution on a nonconstant quadratic $Q$ must have nonconstant $X$.

At any prime $p$ in the table below, set $h = \max_{i > 0,\, X_i \ne 0}(-v_p(X_i)/i)$, choose $\lambda$ of valuation $h$ in a totally ramified extension of $\mathbb{Q}_p$, and substitute $s = \lambda T$. The residue field stays $\mathbb{F}_p$, and $X(\lambda T)$ becomes $p$-integral with a nonconstant reduction. Because the two factors of $2 - X^3$ have constant terms 1 and 2 (both $p$-adic units), each has minimum coefficient valuation at most 0. Those minima add under multiplication and their product is integral, so both factors (and hence their difference $QE^2$) are integral. Applying the same reasoning to $Q$ and $E$ (both with constant term 1) shows $Q(\lambda T)$ and $E(\lambda T)$ are integral too. When $k = 3B^2$, the reduced quadratic coefficient still has the form $3b^2$ because $B\lambda$ is integral.

[reflected_factor.py](reflected_factor.py) enumerates every nonconstant $X \in \mathbb{F}_p[T]$ up to scaling $T \mapsto cT$ ($c \ne 0$). For each $X$, it factors $2 - X^3$ and tests every divisor $Z$ with $Z(0) = 1$ such that both $Z$ and $(2 - X^3)/Z$ have degree at most 6. To split their difference as $QE^2$ with $Q(0) = E(0) = 1$, it takes the odd-multiplicity squarefree part as $Q$, and when that part is constant it also tries moving a squared linear factor from $E^2$ into $Q$. The degree bounds on $Q$ and $E$ make this exhaustive.

At every one of the six primes, every surviving quadratic $Q$ has a nonzero linear coefficient. This rules out $A = 0$ completely. For normalized $Q = 1 + s + ks^2$, the rescaled linear coefficient is $\lambda$, so $v_p(\lambda) = 0$. Therefore the original chart is automatically $p$-integral (no good-reduction assumption is needed), and its reduction appears among the records normalized to linear coefficient 1. As an independent cross-check at $p = 7$, the script also enumerates $X, E, Q$ directly and tests whether $Q^2 E^4 + 8 - 4X^3$ is a square.

| Prime | Positive $k$ of height $\le 1000$ surviving cumulatively | Positive $B$ of height $\le 1000$ surviving cumulatively |
| ---: | ---: | ---: |
| 7 | 228387 | 304501 |
| 13 | 65136 | 130501 |
| 19 | 25931 | 45623 |
| 37 | 12193 | 16724 |
| 67 | 4176 | 5637 |
| 79 | 891 | 980 |

## Exact lifts

At $p = 79$, there are 66 normalized residue records with arbitrary quadratic coefficient and 33 in square class 3. At every record, the 12 nonconstant equations of $X^3 + Z^2 + QE^2 Z = 2$ have an invertible Jacobian in the 12 nonconstant coefficients of $X, E, Z$ at fixed $k$ (whose columns are the shifts of $3X^2$, $2QEZ$, and $2Z + QE^2$).

For each surviving parameter, [reflected_factor.py](reflected_factor.py) lifts every matching residue using this invertible Jacobian to modulus $79^m > 2(10^{60})^2$ and runs exact rational reconstruction against the height bound $10^{60}$. Across all 3,474 lifts for the 891 surviving values of $k$ and all 4,581 lifts for the 980 surviving values of $B$, no exact rational identity survives.

```sh
uv run --with python-flint==0.9.0 python reflected_factor.py --check-seven
uv run --with python-flint==0.9.0 python reflected_factor.py --general --parameter-height 1000
uv run --with python-flint==0.9.0 python reflected_factor.py --parameter-height 1000
lake -d .. env lean ReflectedOrdinate.lean
```
