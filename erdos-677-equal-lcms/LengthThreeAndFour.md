# Erdős #677 at lengths three and four

Write $M(n,k)$ for the LCM of $n+1,\ldots,n+k$. For starts $n<m$, Lean proves that $M(n,3)=M(m,3)$ only for $(n,m)=(2,3)$, and $M(n,4)=M(m,4)$ only for $(n,m)=(1,2)$. In both cases the common LCM is 60 and the blocks overlap, so disjoint blocks of length three or four never have equal LCMs. Neither proof relies on external computation. Both results were known earlier; see the [prior-art audit](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers) and the [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean).

## Length three

The product $(n+1)(n+2)(n+3)$ equals $M(n,3)\gcd(2,n+3)$ and strictly increases with $n$. A collision with $n<m$ therefore needs $n$ even, $m$ odd, and a later product twice the earlier one. With $x=n+2$ and $y=m+2$, this becomes

$$
y^3-y=2(x^3-x),\qquad x\text{ even},\quad y\text{ odd}.
$$

Put $g=\gcd(x,y)$, $x=gx_1$, $y=gy_1$, and $r=y_1^3-2x_1^3$. Dividing by $g$ gives $g^2r=y_1-2x_1$, so $r$ divides $y_1-2x_1$ and thus $6x_1^3=r-(y_1-2x_1)(y_1^2+2x_1y_1+4x_1^2)$. Since $r$ is odd and coprime to $x_1$, we have $r\in\lbrace\pm1,\pm3\rbrace$.

Let $\theta^3=2$. Then $r$ is the norm of $y_1-x_1\theta$ in $\mathbb Z[\theta]$, where $N(a+b\theta+c\theta^2)=a^3+2b^3+4c^3-6abc$. We need two facts about this ring (proved in [BlockLCM/CubeRootTwo.lean](BlockLCM/CubeRootTwo.lean)):

1. Every element of norm $\pm1$ has the form $\pm(\theta-1)^k$. For $u=a+b\theta+c\theta^2$ evaluated at the real cube root,
   $$
   2N=u\bigl((a-b\theta)^2+(b\theta-c\theta^2)^2+(c\theta^2-a)^2\bigr).
   $$
   A norm-one element has $u>0$, and multiplying by a power of $\theta-1$ moves $u$ into $[1,1+\theta+\theta^2)$. There the three squares sum to at most 2, forcing $a,b,c\in\lbrace 0,1\rbrace$. Among those eight triples, only $1$ has norm one and lies in the interval.
2. Every element whose norm is divisible by 3 is a multiple of $1+\theta$, since $N\equiv a-b+c\pmod 3$.

So $y_1-x_1\theta$ is $\pm(\theta-1)^k$ or $\pm(1+\theta)(\theta-1)^k$ for some integer $k$, and its coefficient of $\theta^2$ is zero. Write $k=k_0\pm9n$ with $0\le k_0<9$ and $n\ge0$. Both $(\theta-1)^9$ and $(\theta-1)^{-9}$ have the form $1+9D$. If $3^v$ divides $n$, then

$$
(1+9D)^n\equiv1+9nD+81\binom n2D^2\pmod{3^{v+5}}.
$$

Comparing coefficients of $\theta^2$ across all 36 classes (two multipliers, nine residues $k_0$, and two signs) leads to one of two outcomes. Either the coefficient is nonzero modulo 9 or 81, or $3^v\mid n$ implies $3^{v+1}\mid n$, which forces $n=0$. Lean checks which outcome applies in each class. The coefficient therefore vanishes only for $k\in\lbrace 0,1\rbrace$ with multiplier $1$ and for $k\in\lbrace 0,3\rbrace$ with multiplier $1+\theta$.

These exponents give $x_1\in\lbrace 0,\pm1\rbrace$ or $(x_1,y_1)=\pm(4,5)$. Since $x_1$ is even and positive, $(x_1,y_1)=(4,5)$. Substituting into $g^2r=y_1-2x_1$ gives $-3g^2=-3$, so $g=1$ and $(n,m)=(2,3)$ (see [BlockLCM/Three.lean](BlockLCM/Three.lean)).

## Length four

The product $(n+1)(n+2)(n+3)(n+4)$ equals $M(n,4)$ times 6 if $n\equiv2\pmod 3$ and times 2 otherwise. A collision with $n<m$ therefore needs $n\not\equiv2\pmod 3$, $m\equiv2\pmod 3$, and a later product three times the earlier one.

Put $s(n)=n^2+5n+5$. The product is $s(n)^2-1$, so $x=s(m)$ and $y=s(n)$ satisfy

$$
x^2-3y^2=-2,\qquad 4x+5=(2m+5)^2,\qquad 4y+5=(2n+5)^2,
$$

with $x\equiv1\pmod 3$ and $y\equiv2\pmod 3$.

By descent, the positive solutions of $x^2-3y^2=-2$ are $x+y\sqrt3=(1+\sqrt3)(2+\sqrt3)^k$ for $k\ge0$. Modulo 39 they repeat with period 12 in $k$. The conditions modulo 3 leave $k\equiv2$ or $8\pmod{12}$. At $k\equiv8$, $4x+5$ is 7 modulo 13, which is not a square, so $k\equiv2\pmod{12}$.

Suppose $k\ne2$ and write $k=2+2\cdot2^tj$ with $j$ odd and $t\ge1$. Let $u_t$ be the rational part of $(2+\sqrt3)^{2^t}$, so $u_1=7$ and $u_{t+1}=2u_t^2-1$. Then $u_t$ is 7 or 97 modulo 156. It divides $(2+\sqrt3)^{2\cdot2^tj}+1$, giving

$$
x+y\sqrt3\equiv-(19+11\sqrt3)\pmod{u_t},\qquad 4y+5\equiv-39\pmod{u_t}.
$$

The Jacobi symbol $(-39\mid u_t)$ equals $-1$ for both residues of $u_t$, so $4y+5$ is not a square. Hence $k=2$, which gives $(x,y)=(19,11)$ and $(n,m)=(1,2)$ (see [BlockLCM/Four.lean](BlockLCM/Four.lean)).

The product equation alone has a second solution, $7\cdot8\cdot9\cdot10=3\cdot5\cdot6\cdot7\cdot8$, at $k=3$. Its LCMs are 2520 and 840, and the conditions modulo 3 rule it out.

## Verification

With Elan installed, run the following in the project directory:

```sh
lake exe cache get
lake build
printf '%s\n' 'import BlockLCM' '#print axioms Erdos677.three_collision_iff' '#print axioms Erdos677.four_collision_iff' | lake env lean --stdin
```

Both theorems depend only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.
