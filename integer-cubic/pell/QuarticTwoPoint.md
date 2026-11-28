# Two prescribed values on the Pell conic

One direct way to produce infinitely many integer solutions to $z^2 + y^2 z + x^3 = 2$ would be a quartic rational polynomial map $(x, y, z)$ on the Pell conic $u^2 - 3v^2 = 1$ that sends $(1, 0)$ to the seed $(0, 1, 1)$ and sends the next fundamental Pell point $(2, 1)$ to a second integer solution with a different $x$-coordinate. Here we test the two smallest candidate targets at $(2, 1)$—namely **$(1, 0, -1)$** and **$(-2, 3, 1)$**—and prove that **neither target can occur**, even with arbitrary rational denominators in the polynomial coefficients.

Both obstructions are purely $2$-adic (they already fail over $\mathbb{Q}_2$). We also record the exact rational elimination system, prove that two marked points automatically force $13$-integrality, compute the complete mod-$7$ and mod-$13$ censuses with $p$-adic lifts to $p^{50}$, and run an auxiliary mod-$5$ check for the candidate target $(8, 7, -15)$.

## The 2-adic obstruction (covering arbitrary denominators)

Suppose $x, y, z$ are rational polynomials on $u^2 - 3v^2 = 1$ of total degrees at most $4, 3, 6$, respectively, satisfying $z^2 + y^2 z + x^3 = 2$ identically and taking $(0, 1, 1)$ at $(1, 0)$.

### The big idea: balancing powers of 2

How can a finite list of congruences modulo $4$, $8$, or $4096$ rule out rational polynomials whose denominators contain *arbitrarily high* powers of $2$? We change to a coordinate $w$ that vanishes at both marked points and measure the steepest rate $h$ at which $2$-adic denominators grow with degree:

* If $h \le 1/2$, the conic relation absorbs every power of $2$ back into the original $2$-integral Pell ring, where finite congruences (mod $4$ or mod $4096$) yield a contradiction.
* If $h > 1/2$, rescaling by powers of $2$ isolates a finite list of **17** normalized congruence systems modulo $8$, and every one of them is inconsistent.

### Step 1: A coordinate vanishing at both marks

Set $w = u - 1 - v$. Check that $w = 0$ at both marked points: at $(1, 0)$ we have $(w, v) = (0, 0)$, and at $(2, 1)$ we have $(w, v) = (0, 1)$. Substituting $u = 1 + v + w$ into $u^2 - 3v^2 = 1$ gives the monic quadratic relation
$$
v^2 = (1 + w)v + w + \frac{w^2}{2}.
$$
Reducing powers of $v$ repeatedly by this relation writes each coordinate of degree bound $d$ uniquely as
$$
P(w) + vQ(w), \qquad \deg P \le d, \quad \deg Q < d.
$$
Evaluating at $(w, v) = (0, 0)$ and $(0, 1)$ fixes the integer constant terms $P(0)$ and $Q(0)$ for all three coordinates.

Let $h$ be the maximum of $-v_2(a_i)/i$ over all nonzero positive-degree coefficients $a_i$ across the six polynomials $P, Q$ (where $v_2$ is the $2$-adic valuation). If all six polynomials are constant, the integral case below applies immediately.

### Step 2: Small slopes ($h \le 1/2$)

When $h \le 1/2$, every degree-$i$ coefficient satisfies $2^{\lfloor i/2 \rfloor} a_i \in \mathbb{Z}_2$. Rewriting the conic relation as
$$
\frac{w^2}{2} = v^2 - v - (1 + v)w
$$
shows that every term $a_i w^i$ lands back inside the original $2$-integral Pell-coordinate ring without raising the degree bound.

Writing each coordinate in the normal form $f(v) + wq(v)$ with marked values $a$ at $v = 0$ and $b$ at $v = 1$ gives
$$
f(v) = a + (b - a)v + v(v - 1)r(v).
$$
Comparing coefficients yields a contradiction:

* **modulo $4$** for target $(1, 0, -1)$, and
* **modulo $4096$** for target $(-2, 3, 1)$ (while the latter does admit an explicit model modulo $2048$).

See [TwoPointMarkedPolynomial.lean](TwoPointMarkedPolynomial.lean) for the normal form and [two_point_alternate_two.lean](two_point_alternate_two.lean) for the mod-$4096$ impossibility proof and mod-$2048$ witness.

### Step 3: Large slopes ($h > 1/2$)

When $h > 1/2$, split $h$ into its integer and reduced fractional parts:
$$
h = k + \frac{j}{e} \qquad (k \in \mathbb{Z}_{\ge 0},\; 0 \le j < e,\; \gcd(j, e) = 1,\; \text{allowing } j = 0, e = 1).
$$
An index $i$ achieving the maximum slope $h$ satisfies $v_2(a_i) = -hi \in \mathbb{Z}$, so $e \mid i$ and therefore $e \le 6$.

Switch to the normalized basis $E_i = w^i / 2^{\lfloor hi \rfloor}$. In this basis:

1. Every coefficient becomes $2$-integral, and at least one positive-index coefficient with $e \mid i$ is **odd** (an "active" index).
2. Basis elements multiply according to
   $$
   E_a E_b = 2^{\lfloor h(a + b) \rfloor - \lfloor ha \rfloor - \lfloor hb \rfloor} E_{a + b},
   $$
   whose exponent of $2$ depends only on the fractional part $j/e$.
3. In the conic relation for $v^2$, multiplying by $w$ and $w^2/2$ brings in extra factors of $2$:
   * When $k \ge 1$, writing $2^k = 2H$ and $2^{2k - 1} = 2H^2$ with an arbitrary $2$-adic residue $H$ covers **all** $k \ge 1$ in a single congruence test for each fraction $j/e$.
   * When $k = 0$ and $j/e > 1/2$, all products remain $2$-integral in this basis directly.

There are **12** reduced fractions in $[0, 1)$ with denominator at most $6$: all $12$ require the $k \ge 1$ check, and the $5$ fractions strictly greater than $1/2$ ($3/5, 2/3, 3/4, 4/5, 5/6$) also require the $k = 0$ check—a total of **17** systems per target.

### Formal verification and stronger consequences

* **Lean and Z3 certification:** For each target, [TwoPointBalanced.lean](TwoPointBalanced.lean) proves in Lean that all $17$ systems are inconsistent modulo $8$ and that this list exhausts every admissible fraction. The Lean theorem takes all $23$ unknown coefficients and $H$ as inputs, assuming the cubic identity and an odd coefficient at an active index. An independent Z3 script in [two_point_two_adic.py](two_point_two_adic.py) reproduces all $17$ checks. Passing from rational $2$-adic valuations to these $17$ normalized systems is the written step above.
* **Stronger rule-out for the first target:** If all three coordinates at $(2, 1)$ are integral at $2$, then **$x(2, 1)$ must be even**. Modulo $4$, the cubic equation permits only four odd-$x$ triples, and an exhaustive Python check matches every resulting correction matrix to one of $26$ Lean-certified inconsistent subsystems; see [TwoPointPrimaryTwo.md](TwoPointPrimaryTwo.md).
* **Stronger rule-out for the alternate target:** Because the tests only inspect the marked values modulo a divisor of $4096$, the same proof rules out every integral triple congruent to $(-2, 3, 1) \pmod{4096}$; see [TwoPointAlternateTwo.md](TwoPointAlternateTwo.md).

## Exact elimination equations and the Pell recurrence

In the rational chart $t = v/(u + 1)$ with $L = 1 - 3t^2$, write $x = X/L^4$, $y = Y/L^3$, $z = Z/L^6$, with numerator degrees at most $8, 6, 12$.

To put the two marked points $t = 0$ (corresponding to $(1, 0)$) and $t = 1/3$ (corresponding to $(2, 1)$) in symmetric positions at $0$ and $\infty$, substitute $t = s/(1 + 3s)$. The denominator transforms to $D = 1 + 6s + 6s^2$. Completing the square in $Z$ via $W = 2Z + Y^2$ rewrites the surface identity as
$$
W^2 = Y^4 + 8D^{12} - 4X^3.
$$

Because $s = 0$ and $s = \infty$ are marked, both the constant and leading coefficients of $X, Y, W$ are fixed; in particular,
$$
W_0 = 3, \qquad W_{12} = 6^6 (2z_1 + y_1^2),
$$
both of which are nonzero for both targets. This lets us eliminate $W$ completely:

1. Matching coefficients of $s^1, \ldots, s^6$ solves sequentially for $W_1, \ldots, W_6$ (dividing by $2W_0$ at each step).
2. Matching coefficients of $s^{23}, \ldots, s^{19}$ solves sequentially for $W_{11}, \ldots, W_7$ (dividing by $2W_{12}$ at each step).
3. The remaining **12 middle coefficients** yield $12$ exact polynomial equations over $\mathbb{Q}$ in the $7$ free coefficients of $X$ and $5$ of $Y$, with $Z = (W - Y^2)/2$; see [two_point_elimination.py](two_point_elimination.py).

**Why two-point charts matter:** For *any* future chart of these degrees through an integral seed whose $x$-value changes at $t = 1/3$, Lean proves in [MixedPellAmplification.lean](MixedPellAmplification.lean) that a rational polynomial identity generates infinitely many distinct integer solutions: the Pell recurrence $(u, v) \mapsto (2u + 3v, u + 2v)$ returns to the seed modulo any common denominator along an infinite subsequence.

## Residue calculations at 7 and 13 (and $(8, 7, -15)$ at 5)

### Why two marked points force 13-integrality

Remarkably, having two marked points eliminates denominators at $13$ automatically, with no height bound:

1. In the $t$-chart, the two marks $c = 0$ and $c = 1/3$ reduce to distinct elements of $\mathbb{F}_{13}$, and $L(c) = 1 - 3c^2$ is a $13$-adic unit at both ($L(0) = 1$, $L(1/3) = 2/3$).
2. Suppose for contradiction that some coefficient of $X, Y, Z$ has negative $13$-adic valuation. Because integral shifts $t \mapsto t + c$ preserve the minimum coefficient valuation, at either center $c$ the positive-index Taylor coefficients have a strictly positive maximum slope $h = \max(-v_{13}(a_i)/i)$.
3. Rescaling $t = c + \lambda T$ with $v_{13}(\lambda) = h$ in a totally ramified extension makes $L$ reduce to the nonzero constant $L(c)$ and yields a nonconstant ordinary polynomial solution over $\mathbb{F}_{13}$. By [OrdinaryPolynomial.md](OrdinaryPolynomial.md), the reduced $x$-coordinate must have degree at least $6$.
4. Therefore, at each center $c$, some Taylor coefficient $a_k$ of $X$ with $k \ge 6$ satisfies $v_{13}(a_k) = -kh$, while every nonzero earlier coefficient ($i < k$) satisfies $v_{13}(a_i) \ge -ih > -kh$.
5. Scale $X$ by a power of $13$ so its minimum coefficient valuation is $0$ (preserved by integral shifts). Its nonzero reduction modulo $13$ would then vanish to order at least $6$ at **two** distinct points of $\mathbb{F}_{13}$, despite having degree at most $8$—impossible since $6 + 6 > 8$.

Hence every rational solution of arbitrary height is $13$-integral and appears in the mod-$13$ census. Lean formalizes the multiplicity and slope lemmas in [TwoPointDegree.lean](TwoPointDegree.lean).

### Mod-7 and mod-13 censuses and local lifts

Fixing the $x$-values at both marks leaves $7$ free coefficients in $X$. Across all $p^7$ candidates over $\mathbb{F}_p$, [two_point_census.py](two_point_census.py) factors $2L^{12} - X^3$, checks every degree-$12$ divisor $Z$ with $Z(0) = 1$, and tests whether $(2L^{12} - X^3)/Z - Z$ is a square matching both $y$-values.

At both $p = 7$ and $p = 13$, $2$ is not a cube modulo $p$, so $2L^{12} - X^3$ keeps full degree $24$ and nonzero constant and marked values (candidates that lose poles modulo $p$ are included):

* **Target $(1, 0, -1)$:** $2$ residue triples modulo $7$, and $4$ modulo $13$.
* **Target $(-2, 3, 1)$:** $1$ residue triple modulo $7$, and $4$ modulo $13$.

[two_point_lifts.py](two_point_lifts.py) lifts every residue in [two_point_residues.jsonl](two_point_residues.jsonl) to precision $p^{50}$. The $2$-adic obstruction above proves that none of these local lifts can come from a rational substitution.

### An extra test: target $(8, 7, -15)$

As a sanity check on a third point of the cubic surface, $(8, 7, -15)$ satisfies $8^3 + 7^2(-15) + (-15)^2 = 2$, and its quartic system **does** admit a solution modulo $4096$ (verified in [two_point_alternate_two.lean](two_point_alternate_two.lean)). However, testing all $5^7 = 78{,}125$ numerators $X$ over $\mathbb{F}_5$ in [two_point_census.py](two_point_census.py) finds **zero** models, so any rational chart through $(8, 7, -15)$ would require a denominator divisible by $5$ in the $t$-chart.

## Reproduction

```sh
lake -d .. build
uv run --with z3-solver==4.15.4.0 python two_point_two_adic.py
uv run --with python-flint==0.9.0 python two_point_primary_two.py
uv run --with python-flint==0.9.0 python two_point_alternate_balanced_two.py
uv run --with python-flint==0.9.0 python two_point_elimination.py --target 1
uv run --with python-flint==0.9.0 python two_point_census.py --prime 5 --endpoint 8 7 -15
uv run --with python-flint==0.9.0 python two_point_lifts.py two_point_residues.jsonl --precision 50
```
