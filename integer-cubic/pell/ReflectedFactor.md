# Reflections fixing the abscissa and last coordinate

Among quartic Pell substitutions for $z^2 + y^2 z + x^3 = 2$ passing through $(0, 1, 1)$, a natural symmetric family arises when a reflection of the Pell conic leaves $x$ and $z$ fixed and negates $y$. Algebraically, this means $x = X(s)$ and $z = Z(s)$ are ordinary polynomials in a quotient coordinate $s$, while $y = r E(s)$ with $r^2 = Q(s)$ a quadratic polynomial in $s$.

Using six finite-field sieves (at primes $7, 13, 19, 37, 67, 79$) together with an automatic $p$-integrality argument, we obtain both height-free and large-height exclusions for this family—with **no assumption** on any second marked point:

* **Height-free parameter exclusions** (valid for *arbitrary* rational coefficients in $X, E, Z$):
  * Every quadratic $Q = 1 + As + Cs^2$ with $A = 0$ is impossible in characteristic zero.
  * Every positive nonsquare parameter $k$ (in normalized $Q = 1 + s + ks^2$) with height $h(k) \le 30$ is ruled out (the first passing parameter by height is $31$).
  * Every Pell-conic parameter $k = 3B^2$ (corresponding to $u^2 - 3v^2 = 1$) with $B \ne 0$ and $h(B) \le 18$ is ruled out (the first positive passing $B$ is $19/2$).
* **Height-$10^{60}$ lifting exclusions:** Lifting all surviving parameters modulo $79^m$ rules out every nonconstant identity in which all $12$ nonconstant coefficients of $X, E, Z$ have height at most $10^{60}$, across all positive rational $k$ with $h(k) \le 1000$ and separately across all $k = 3B^2$ with $h(B) \le 1000$.

## Setup and Pell parametrization

Consider a rational substitution through $(0, 1, 1)$ of the form
$$
x = X(s), \qquad y = r E(s), \qquad z = Z(s), \qquad r^2 = Q(s),
$$
where $\deg X \le 4$, $\deg E \le 2$, $\deg Z \le 6$, the constant terms are $(X(0), E(0), Z(0)) = (0, 1, 1)$ (with $Q(0) = 1$), and any second marked point is left free. Substituting into $z^2 + y^2 z + x^3 = 2$ gives
$$
Z(Z + Q E^2) = 2 - X^3.
$$

Write the quadratic factor as $Q(s) = 1 + As + Cs^2$. The modular check below rules out $A = 0$ in characteristic zero. Whenever $A \ne 0$, rescaling the coordinate via $s \mapsto As$ normalizes the quadratic to
$$
Q(s) = 1 + s + ks^2.
$$
How does this connect to Pell conics?

* On $u^2 - 3v^2 = 1$, this normalization yields $k = 3B^2$ for some nonzero rational $B$.
* More generally, **any** positive nonsquare rational $k$ corresponds to the Pell conic $u^2 - kv^2 = 1$: setting
  $$
  s = \frac{u + 2kv - 1}{2k}, \qquad r = u + \frac{v}{2}
  $$
  satisfies $r^2 = 1 + s + ks^2$ identically and maps $(u, v) = (1, 0)$ to $(s, r) = (0, 1)$.

Lean verifies this parametrization and checks that every reflected-factor identity solves the cubic surface equation in [ReflectedOrdinate.lean](ReflectedOrdinate.lean). Throughout, we measure rational heights by $h(a/b) = \max(|a|, b)$ in lowest terms (with $b > 0$).

## Automatic $p$-integrality and the six modular sieves

Why do finite-field checks at six primes apply to rational polynomials with *arbitrary* denominators? The key is a valuation-rescaling argument showing that $Q$'s linear term cannot vanish modulo $p$, which automatically forces $p$-integrality.

1. **$X$ must be nonconstant.** If $X$ is constant, then $X = 0$, so $Z(Z + Q E^2) = 2$ forces both factors to be constant, giving $Z = 1$ and $Q E^2 = 1$. Thus any nonconstant substitution on a nonconstant quadratic $Q$ must have nonconstant $X$.
2. **Balancing denominators at a prime $p$.** For any prime $p$ in the table below, set $h = \max_{i > 0,\, X_i \ne 0}(-v_p(X_i)/i)$, pick $\lambda$ of valuation $h$ in a totally ramified extension of $\mathbb{Q}_p$, and substitute $s = \lambda T$. The residue field stays $\mathbb{F}_p$, and $X(\lambda T)$ becomes $p$-integral with a nonconstant reduction modulo $p$.
3. **Integrality propagates to $Z, Q, E$.** The two factors $Z$ and $Z + QE^2$ of $2 - X^3$ have constant terms $1$ and $2$ (both $p$-adic units), so each has minimum coefficient valuation at most $0$. Because minimum valuations add under polynomial multiplication (multiplicativity of the Gauss norm) and their product $2 - X^3$ is integral, both factors—and hence their difference $QE^2$—must be integral. Repeating the same argument for $Q$ and $E$ (both with constant term $1$) shows $Q(\lambda T)$ and $E(\lambda T)$ are integral too. When $k = 3B^2$, the reduced quadratic coefficient still has the form $3b^2$ because $B\lambda$ is integral.
4. **Exhaustive enumeration over $\mathbb{F}_p$.** [reflected_factor.py](reflected_factor.py) enumerates every nonconstant $X \in \mathbb{F}_p[T]$ up to scaling $T \mapsto cT$ ($c \ne 0$). For each $X$, it factors $2 - X^3$ and tests every divisor $Z$ with $Z(0) = 1$ such that $\deg Z \le 6$ and $\deg((2 - X^3)/Z) \le 6$. To split the difference $(2 - X^3)/Z - Z$ as $Q E^2$ with $Q(0) = E(0) = 1$, it takes the odd-multiplicity squarefree part as $Q$, and whenever that part is constant it also tries shifting a squared linear factor from $E^2$ into $Q$. The degree bounds on $Q$ and $E$ make this completely exhaustive.
5. **No good-reduction hypothesis is needed.** At every one of the six primes, **every** surviving quadratic $Q$ has a nonzero linear coefficient. This rules out $A = 0$ immediately. For normalized $Q = 1 + s + ks^2$, the rescaled linear coefficient is $\lambda$, so $v_p(\lambda) = 0$. Therefore the original rational chart is *automatically $p$-integral*, and its reduction must appear among the records normalized to linear coefficient $1$.

As an independent cross-check at $p = 7$, the script also enumerates $X, E, Q$ directly and tests whether $Q^2 E^4 + 8 - 4X^3$ is a square. The cumulative sieve counts across parameters of height at most $1000$ are:

| Prime | Positive $k$ of height $\le 1000$ surviving cumulatively | Positive $B$ of height $\le 1000$ surviving cumulatively |
| ---: | ---: | ---: |
| 7 | 228387 | 304501 |
| 13 | 65136 | 130501 |
| 19 | 25931 | 45623 |
| 37 | 12193 | 16724 |
| 67 | 4176 | 5637 |
| 79 | 891 | 980 |

## Exact lifts modulo $79^m$

At $p = 79$, there are **66** normalized residue records with arbitrary quadratic coefficient and **33** in square class $3$. At every record, the $12$ nonconstant coefficient equations of $X^3 + Z^2 + Q E^2 Z = 2$ have an invertible $12 \times 12$ Jacobian with respect to the $12$ nonconstant coefficients of $X, E, Z$ at fixed $k$ (whose columns are the shifts of $3X^2$, $2QEZ$, and $2Z + Q E^2$).

For every parameter surviving the six-prime sieve, [reflected_factor.py](reflected_factor.py) Hensel-lifts each matching mod-$79$ residue to modulus $79^m > 2(10^{60})^2$ and applies exact rational reconstruction against the height bound $10^{60}$:

* Across all **3,474** lifts for the **891** surviving values of $k$, zero exact rational identities survive.
* Across all **4,581** lifts for the **980** surviving values of $B$, zero exact rational identities survive.

## Reproduction

```sh
uv run --with python-flint==0.9.0 python reflected_factor.py --check-seven
uv run --with python-flint==0.9.0 python reflected_factor.py --general --parameter-height 1000
uv run --with python-flint==0.9.0 python reflected_factor.py --parameter-height 1000
lake -d .. env lean ReflectedOrdinate.lean
```
