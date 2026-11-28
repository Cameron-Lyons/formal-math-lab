# Quintic substitutions with a quadratic in the pole-one coordinate

In the quintic Pell substitution $z = (2 - r^3)/a$, $x = r + qz$ for the cubic surface $z^2 + y^2 z + x^3 = 2$, a natural special case is to take $q$ to be an ordinary quadratic polynomial in the pole-one coordinate $r$ itself. Here we prove that **for every marked value $R \in \{0, 1, -1, 2, -2\}$ of $r$, there is no such quintic substitution through $(0, 1, 1)$**.

The coefficients of $q$ are completely unrestricted (no height bound is assumed), and the obstruction holds over any algebraically closed field of characteristic zero. All exact discriminants and squarefree decompositions below can be reproduced with [quintic_invariant_elimination.py](quintic_invariant_elimination.py).

## Setup and polynomial reduction

Let $r$ be a function with simple poles at both ends of a Pell conic, let $R$ be its value at the marked point, and set
$$
a = 2 - R^3, \qquad z = \frac{2 - r^3}{a}, \qquad x = r + qz.
$$
At the marked point we want $(x, y, z) = (0, 1, 1)$, which forces $q(R) = -R$. Because $q$ is a quadratic polynomial in $r$, we can expand it around $R$ as
$$
q(r) = -R + b(r - R) + c(r - R)^2,
$$
where $c \ne 0$ is required for $x$ to be genuinely quintic (pole order $5$). Setting $h = 2 - r^3$ and clearing $a^2$, the cubic surface equation $z^2 + y^2 z + x^3 = 2$ becomes
$$
F(r) = a^2 y^2 = a^3 - ah - 3a^2 r^2 q - 3arq^2 h - q^3 h^2.
$$
Notice that $F$ is a degree-$12$ polynomial in $r$ with leading coefficient $-c^3 \ne 0$.

## Proof strategy: Riemann–Hurwitz and iterated discriminants

Because $F(r)$ depends only on $r$, it must become a square when pulled back along the degree-$2$ map $r$ from the conic to $\mathbb{P}^1$. That geometric constraint forces $F(r)$ to have many repeated roots—so many that eliminating $r$ via a first discriminant leaves a polynomial with a high-multiplicity root in $c$, and eliminating $c$ via a second discriminant forces $b = 0$, which fails immediately.

### Step 1: Bounding distinct roots via Riemann–Hurwitz

As a morphism from the smooth projective conic ($\cong \mathbb{P}^1$) to $\mathbb{P}^1$, the function $r$ has degree $2$. By the Riemann–Hurwitz formula, a degree-$2$ map $\mathbb{P}^1 \to \mathbb{P}^1$ has exactly **two** geometric branch points.

Because the pullback of $F(r)$ to the conic is a square ($a^2 y^2$), every odd-multiplicity root of $F$ must be one of those two branch values—otherwise the pullback would have odd vanishing order at the two unramified preimages. Hence $F$ has **at most two odd-multiplicity roots**.

Now count total roots by degree:
* $\deg F = 12$ (with nonzero leading coefficient $-c^3$),
* each odd-multiplicity root uses degree at least $1$, and
* each even-multiplicity root uses degree at least $2$.

Putting as many roots as possible into the smallest multiplicities ($2$ simple roots and $5$ double roots) gives **at most $7$ distinct roots in total**, and therefore
$$
\deg \gcd(F, F') \ge 12 - 7 = 5.
$$

### Step 2: Sylvester corank forces high-order vanishing of the discriminant

In any one-parameter family of polynomials of fixed degree whose leading coefficient stays a unit at a specialized parameter value, the discriminant vanishes there to order at least $\deg \gcd(F, F')$:

1. The Sylvester matrix of $F$ and $F'$ has corank equal to $\deg \gcd(F, F')$.
2. The determinant of any matrix family that drops rank by $d$ at a parameter value vanishes there to order at least $d$.
3. Passing from the resultant $\det(\mathrm{Syl}(F, F'))$ to the discriminant divides by the leading coefficient, which is a unit and preserves vanishing order.

### Step 3: First elimination (removing $r$)

Apply Step 2 to the parameter $c$ at fixed $b$. At any solution, $\operatorname{disc}_r(F)$ must vanish to order at least $5$ in $c$.

Dividing $\operatorname{disc}_r(F)$ by a nonzero integer and the trivial factor $c^{18}$ produces a polynomial $D(b, c)$ with the same vanishing orders at every $c \ne 0$. When $R = 0$, $D$ turns out to be a polynomial purely in $C = c^3$, and substituting $c \mapsto c^3$ also preserves root multiplicities away from $c = 0$. Uniformly write
$$
v = \begin{cases} c^3 & \text{if } R = 0, \\ c & \text{if } R \in \{1, -1, 2, -2\}. \end{cases}
$$

### Step 4: Second elimination (removing $v$ and forcing $b = 0$)

In all five cases, the leading coefficient of $D(b, v)$ as a polynomial in $v$ is a nonzero integer independent of $b$, so its degree in $v$ never drops. A root $v \ne 0$ of multiplicity at least $5$ satisfies $\deg \gcd(D, D_v) \ge 4$. Applying the same Sylvester argument a second time shows that $b$ must be a root of multiplicity at least $4$ in $\operatorname{disc}_v(D)$.

Computing the exact squarefree factorization of $\operatorname{disc}_v(D)$ gives:

| $R$ | Degree in $b$ of the second discriminant | Squarefree blocks as $(\text{degree}, \text{multiplicity})$ |
| --- | ---: | --- |
| $0$ | 252 | $(1, 9),\; (15, 3),\; (99, 2)$ |
| $1, -1, 2, -2$ | 816 | $(1, 18),\; (48, 3),\; (327, 2)$ |

In every case, the **only** block of multiplicity at least $4$ is the degree-$1$ block, which is $b$ itself—forcing **$b = 0$**.

Finally, after stripping its trivial power of $v$, the specialized polynomial $D(0, v)$ is **squarefree**, so no nonzero $v$ can be a root of multiplicity at least $5$. This rules out the quintic substitution for all five values of $R$.

## Reproduction

```sh
uv run --with python-flint==0.9.0 python quintic_invariant_elimination.py
```
