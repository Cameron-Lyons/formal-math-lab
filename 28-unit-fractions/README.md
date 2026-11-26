# The reciprocal Rado number $f_2(28)=2352$

Every red-blue coloring of $\{1,\ldots,N\}$ has a monochromatic solution to
$1/x_1+\cdots+1/x_{28}=1/y$ exactly when $N\ge2352$. All 29 denominators
have the same color, and repetitions are allowed. This is the $k=28$ case
of [Gaiser and Ramezanpour’s Conjecture 1.3](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem3).

## Upper bound

Color each divisor $t$ of $4704$ with $2\le t\le2352$ by the color of
$4704/t$. A monochromatic sum $t_1+\cdots+t_{28}=s$ gives the required unit
fractions on dividing by $4704$. In an avoiding coloring, $t$ and $28t$
therefore have opposite colors whenever both are in the set.

Call $2$ red. Then $1568=28^2\cdot2$ is red. If $3$ were blue, $84$ would be
red. The identity $84=14(2+4)$ would force $4$ blue and hence $112$ red.
But then $1568=13\cdot112+84+14\cdot2$ would be a red sum of 28 terms.
Thus $3$ is red, and so is $2352=28^2\cdot3$.

Read the next three rows in order. Each boxed number must be blue because
everything else in its row is red. Dividing it by $28$ gives the next red
number.

| Sum of 28 terms | Next red number |
| --- | --- |
| $1568=9\cdot\boxed{168}+18\cdot3+2$ | $168/28=6$ |
| $2352=1568+\boxed{672}+15\cdot6+11\cdot2$ | $672/28=24$ |
| $1568=\boxed{1176}+13(24+6)+2$ | $1176/28=42$ |

Now every term and the target in the following sum are red.

$$
2352=1568+10\cdot42+15\cdot24+2\cdot2.
$$

The opening pair of identities adapts [Case 1 of Gaiser and Ramezanpour’s Theorem 3.3](https://arxiv.org/html/2607.04373v1#S3.Thmtheorem3).

## Lower bound

On $1,\ldots,2351$, color $3,\ldots,83$ red and the rest blue. Any solution
satisfies $28y\le\max_i x_i$. A red solution would require $y\le2$. A blue
solution would require $y\in\{1,2\}$, so the contribution from blue
denominators at least $84$ would be a multiple of $1/2$ between $0$ and
$28/84=1/3$. It would have to be zero, leaving 28 terms each at least $1/2$.
This is the coloring from [Gaiser and Ramezanpour’s Theorem 1.1](https://arxiv.org/html/2607.04373v1#S1.Thmtheorem1).

## Verification

Run `lake build` from this directory with Lean 4.36.0. The package uses only
the standard library. Lean checks the six sums and the avoiding coloring and
combines them in `UnitFractions28.forces_iff (N : Nat) : Forces N ↔ 2352 ≤ N`.
[Exact threshold](UnitFractions.lean) · [Upper bound](UnitFractions/Upper.lean) ·
[Lower bound](UnitFractions/Lower.lean)
