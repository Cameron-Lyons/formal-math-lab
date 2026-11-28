# Erdős #677 at lengths two and five

Write $M(n, k) = \operatorname{lcm}(n + 1, \ldots, n + k)$ for the least common multiple of $k$ consecutive positive integers. Two ordered blocks starting at $n < m$ are disjoint when $n + k \le m$. This note covers the complete Lean 4 proof for length $k = 2$ and the partial Lean 4 results for length $k = 5$ (where both the unrestricted length-five case and the general conjecture for arbitrary $k > 0$ remain open). See the [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean) and [problem status](https://www.erdosproblems.com/677).

## Length two

Any two consecutive integers $n + 1$ and $n + 2$ are coprime, so
$$M(n, 2) = (n + 1)(n + 2).$$
Because both factors strictly increase with $n$, distinct starts always produce distinct LCMs — there are no collisions at all, overlapping or disjoint ([BlockLCM/Two.lean](BlockLCM/Two.lean)).

## Length five

### Step 1: The defect modulo 12

Define the **overlap defect** $D(n)$ as the product of the five entries divided by their LCM:
$$D(n) = \frac{(n+1)(n+2)(n+3)(n+4)(n+5)}{M(n, 5)}.$$
Only primes smaller than $5$ (namely $2$ and $3$, with powers up to $4$ and $3$) can divide more than one integer in a block of length $5$, so $D(n)$ depends solely on $n \bmod 12$:

| $n \bmod 12$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $D(n)$ | 2 | 12 | 6 | 8 | 6 | 12 | 2 | 24 | 6 | 4 | 6 | 24 |

Because the 5-term product strictly increases with $n$, an equality $M(n, 5) = M(m, 5)$ with $n < m$ forces the later block to have a strictly larger defect: $D(n) < D(m)$. That single comparison rules out **87 of the 144** ordered residue pairs $(n \bmod 12, m \bmod 12)$ for arbitrarily large starts ([BlockLCM/Defect.lean](BlockLCM/Defect.lean)).

### Step 2: Reduction to seven sextic curves

For each surviving pair with $D(n) < D(m)$, write the ratio in lowest terms as $a/b = D(n)/D(m)$, center both blocks at $X = n + 3$ and $Y = m + 3$, and set
$$F(x) = x(x^2 - 1)(x^2 - 4),$$
which is the 5-term product centered at $x$. Lean proves that equal LCMs are equivalent to
$$a F(Y) = b F(X).$$
A collision with $n < m$ therefore yields one of **seven** reduced coefficient pairs $(a, b)$ together with a rational point on an explicit sextic curve ([BlockLCM/Five.lean](BlockLCM/Five.lean)).

### Step 3: Slope-height bound

For a hypothetical collision, define the reduced rational slope
$$\frac{R}{S} = \frac{bX - aY}{Y - X} \quad (\gcd(R, S) = 1), \qquad H = \max(R, S).$$
Two elementary divisibility estimates connect the block size $X$ to the slope height $H$ (following [Danesh and Bianchetti, §6.4](https://ijmttjournal.org/archive/IJMTT-V72I9P101)):

1. **Common-factor bound ([BlockLCM/Scale.lean](BlockLCM/Scale.lean)):** Pull out $c = \gcd(X, Y)$ so $X = cU$ and $Y = cV$ with $\gcd(U, V) = 1$. Expanding $aF(cV) = bF(cU)$ and dividing by $c$ leaves $4(aV - bU)$ as the only term not divisible by $c^2$, forcing $c^2 \mid 4(bU - aV)$. Since $bU - aV$ is positive and strictly smaller than $(b - a)U$ (as $V > U$), we obtain $c^2 \le 4(b - a)U$, and multiplying by $U^2$ yields
   $$X^2 \le 4(b - a)U^3.$$
2. **Slope-coprimality bound ([BlockLCM/Slope.lean](BlockLCM/Slope.lean)):** Substituting $X = cU$ and $Y = cV$ into $(bX - aY)/(Y - X) = R/S$ cancels $c$ and cross-multiplies to $(R + bS)U = (R + aS)V$. Since $\gcd(U, V) = 1$, we have $U \mid (R + aS)$, so
   $$U \le (1 + a)H.$$

Across all seven coefficient pairs $(a, b)$, the prefactor satisfies $4(b - a)(1 + a)^3 \le 352$. Combining the two estimates gives
$$X^2 \le 352 H^3.$$
In particular, whenever $H \le 3 \cdot 10^{12}$, we obtain $n \le 10^{20}$, where an existing Lean theorem already eliminates every disjoint collision ([BlockLCM/HeightBound.lean](BlockLCM/HeightBound.lean) and [Height.lean](Height.lean)). The unrestricted length-five case remains open.

### Step 4: Classification of overlapping blocks

Among overlapping blocks ($n < m < n + 5$), the **only** equal LCMs are
$$(n, m) \in \{(0, 1),\, (4, 5),\, (9, 10),\, (14, 15)\}.$$
Lean proves this by showing $n + 1 < 17(m - n)$ and exhaustively checking the remaining finite range ([BlockLCM/Location.lean](BlockLCM/Location.lean)).

## Verification

With Elan installed, run the following commands in the project directory:

```sh
lake exe cache get
lake build
lake env leanchecker BlockLCM
```
