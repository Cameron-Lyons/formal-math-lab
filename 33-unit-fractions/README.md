# The 33-term reciprocal Rado number is 3267

Every red-blue coloring of $\{1,\ldots,N\}$ contains a monochromatic solution to
$1/x_1+\cdots+1/x_{33}=1/y$, with repetitions allowed, if and only if $N\ge3267$.
This settles $k=33$ in Gaiser and Ramezanpour's Conjecture 1.3. Their Theorem 1.1
gives the lower bound $3k^2$, and their Table 2 gives the odd cases through $k=25$.
[Original paper](https://arxiv.org/html/2607.04373v1)

## Upper bound

If $d$ and $33d$ have the same color, then $1/d=33/(33d)$ is already a solution.
So assume they have opposite colors for $d=1,3,4,9,33,36,99$. Call $36$ red.
Then $1188$ is blue, $1089$ has the color of $1$, and $3267$ has the color of $3$.

**Read down the table and take the first row that applies.** It gives a solution
in the indicated color. Each $m/d$ stands for $m$ copies of $1/d$.

| First condition that holds | Color | Identity |
| --- | --- | --- |
| $3$ red and $27$ blue | Blue | $1/27=1/99+32/1188$ |
| $1$ red and $27$ red | Red | $1=9/27+24/36$ |
| $3$ red | Red | $1/3=2/27+1/33+8/36+22/3267$ |
| $1$ red | Blue | $1/3=6/27+3/33+24/1188$ |
| $2$ red | Red | $1/2=3/33+6/36+24/99$ |
| $4$ red | Blue | $1/2=1/3+21/132+6/1089+1/1188+4/3267$ |
| $9$ blue | Blue | $1/4=2/9+22/1089+9/1188$ |
| Otherwise | Blue | $1=2/3+1/4+23/297+7/1188$ |

For example, if the third row is the first match, $3$ is red. Skipping the
first row means $27$ is red, and skipping the second means $1$ is blue. Thus
$27,33,36,3267$ are all red, as is the target $3$. If the last row is reached,
$1,3,4$ are blue and $9$ is red, so $297$ is blue and the last identity works.
Every row has 33 summands, and $13068$ clears all denominators.

## Lower bound and Lean verification

The existing lower-bound coloring at $3266$ makes $3,\ldots,98$ red and all
other denominators blue. The Lean theorem specializes the general lower bound
to $k=33$ and combines it with the fifteen identities above.
[General lower bound](../even-unit-fractions/EvenUnitFractions/Lower.lean) ·
[Certificate and theorem](UnitFractions33.lean)

Run the following commands from this directory with Lean 4.36.0.

```sh
lake build
lake env leanchecker UnitFractions33
```
