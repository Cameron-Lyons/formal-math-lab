# Erdős #677 at lengths three and four

Write $M(n, k) = \operatorname{lcm}(n + 1, \ldots, n + k)$ for the least common multiple of $k$ consecutive positive integers. This note presents complete, self-contained classifications of all equalities $M(n, k) = M(m, k)$ with $n < m$ for lengths $k = 3$ and $k = 4$, proved purely inside Lean 4 with **no external computation**:

* **Length $k = 3$:** the unique solution is $(n, m) = (2, 3)$, where $\operatorname{lcm}(3, 4, 5) = \operatorname{lcm}(4, 5, 6) = 60$.
* **Length $k = 4$:** the unique solution is $(n, m) = (1, 2)$, where $\operatorname{lcm}(2, 3, 4, 5) = \operatorname{lcm}(3, 4, 5, 6) = 60$.

In both cases the blocks overlap, so **disjoint blocks of length three or four never share an LCM**. Both results were known earlier; see the [prior-art audit](../PRIOR_ART.md#erdős-677-equal-lcms-of-six-consecutive-integers) and the [formal statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/677.lean).

## Length three

**The big idea.** Among three consecutive integers $n+1, n+2, n+3$, the only prime that can divide two of them is $2$, which happens precisely when both endpoints $n+1$ and $n+3$ are even (i.e., $n$ is odd). Thus
$$(n+1)(n+2)(n+3) = M(n, 3) \cdot \gcd(2, n + 3).$$
Since the product strictly increases with $n$, an equality $M(n, 3) = M(m, 3)$ with $n < m$ can happen only when the smaller block has overlap factor $1$ ($n$ even) and the larger block has overlap factor $2$ ($m$ odd) — forcing the larger product to be exactly **twice** the smaller one.

Centering both triples at $x = n + 2$ and $y = m + 2$, the product $(x - 1)x(x + 1) = x^3 - x$ turns this into the cubic Diophantine equation
$$
y^3 - y = 2(x^3 - x), \qquad x \text{ even}, \quad y \text{ odd}.
$$

### Step 1: Reduce to a norm equation in $\mathbb{Z}[\sqrt[3]{2}]$

Factor out $g = \gcd(x, y)$ by writing $x = g x_1$ and $y = g y_1$ with $\gcd(x_1, y_1) = 1$, and set $r = y_1^3 - 2x_1^3$. Dividing $y^3 - y = 2(x^3 - x)$ by $g$ yields
$$g^2 r = y_1 - 2x_1.$$
Thus $r$ divides $y_1 - 2x_1$. By the polynomial identity
$$6x_1^3 = r - (y_1 - 2x_1)(y_1^2 + 2x_1 y_1 + 4x_1^2),$$
$r$ must also divide $6x_1^3$. Because $y$ is odd and $x$ is even, $y_1$ is odd and $x_1$ is even, so $r = y_1^3 - 2x_1^3$ is **odd** and **coprime to $x_1$** (any prime dividing both $r$ and $x_1$ would divide $y_1^3$, contradicting $\gcd(x_1, y_1) = 1$). The only odd divisors of $6x_1^3$ coprime to $x_1$ are
$$r \in \lbrace \pm 1, \pm 3 \rbrace.$$

### Step 2: Units and norm-3 elements in $\mathbb{Z}[\theta]$

Let $\theta = \sqrt[3]{2}$ (so $\theta^3 = 2$). Then $r = y_1^3 - 2x_1^3$ is precisely the algebraic norm $N(y_1 - x_1\theta)$ in the cubic ring $\mathbb{Z}[\theta]$, where
$$N(a + b\theta + c\theta^2) = a^3 + 2b^3 + 4c^3 - 6abc.$$
We use two structural facts about $\mathbb{Z}[\theta]$, formalized in [BlockLCM/CubeRootTwo.lean](BlockLCM/CubeRootTwo.lean):

1. **Classification of units:** Every element of norm $\pm 1$ has the form $\pm(\theta - 1)^k$ for some $k \in \mathbb{Z}$. Indeed, evaluating $u = a + b\theta + c\theta^2$ at the real cube root gives the identity
   $$
   2N = u\bigl((a - b\theta)^2 + (b\theta - c\theta^2)^2 + (c\theta^2 - a)^2\bigr).
   $$
   Any norm-one element therefore has $u > 0$. Since $(\theta - 1)^{-1} = 1 + \theta + \theta^2 > 1$, multiplying by a suitable power of $\theta - 1$ moves $u$ into the fundamental interval $[1, 1 + \theta + \theta^2)$. On that interval, $u \ge 1$ forces the sum of the three squares to be at most $2$, which restricts $a, b, c \in \lbrace 0, 1 \rbrace$. Among those eight triples, only $1$ has norm one and lies in $[1, 1 + \theta + \theta^2)$.
2. **Factorization of norm-3 elements:** Modulo $3$, $N(a + b\theta + c\theta^2) \equiv a - b + c \pmod 3$. Since $\theta \equiv -1 \pmod{1 + \theta}$ and $N(1 + \theta) = 3$, every element whose norm is divisible by $3$ is a multiple of $1 + \theta$.

### Step 3: Kill the $\theta^2$-coefficient by 3-adic expansion

Combining Steps 1 and 2, $y_1 - x_1\theta$ must equal either $\pm(\theta - 1)^k$ or $\pm(1 + \theta)(\theta - 1)^k$ for some integer $k$, with the extra constraint that its **coefficient of $\theta^2$ is zero**.

Write $k = k_0 \pm 9n$ with $0 \le k_0 < 9$ and $n \ge 0$. Modulo $9$, both $(\theta - 1)^9$ and $(\theta - 1)^{-9}$ reduce to $1$, so each has the form $1 + 9D$ for some $D \in \mathbb{Z}[\theta]$. Expanding $(1 + 9D)^n$ by the binomial theorem, if $3^v$ divides $n$ then all terms of degree $\ge 3$ vanish modulo $3^{v+5}$, leaving
$$
(1 + 9D)^n \equiv 1 + 9nD + 81\binom{n}{2}D^2 \pmod{3^{v+5}}.
$$
Inspecting the $\theta^2$-coefficient across all $2 \times 9 \times 2 = 36$ classes (two multipliers $1$ and $1 + \theta$, nine residues $k_0$, and two signs for $\pm 9n$) produces one of two outcomes in every class:
* either the $\theta^2$-coefficient is already nonzero modulo $9$ or $81$,
* or vanishing forces $3^v \mid n \implies 3^{v+1} \mid n$, which by 3-adic descent forces $n = 0$.

Lean checks which outcome applies in each of the 36 classes. Consequently, the $\theta^2$-coefficient vanishes **only** for $k \in \lbrace 0, 1 \rbrace$ with multiplier $1$ and for $k \in \lbrace 0, 3 \rbrace$ with multiplier $1 + \theta$.

Evaluating those four cases gives $x_1 \in \lbrace 0, \pm 1 \rbrace$ or $(x_1, y_1) = \pm(4, 5)$ (since $(1 + \theta)(\theta - 1)^3 = -5 + 4\theta$). Because $x_1$ is even and positive, $(x_1, y_1) = (4, 5)$ is the sole solution. Substituting into $g^2 r = y_1 - 2x_1$ yields $-3g^2 = -3$, so $g = 1$, $x = 4$, $y = 5$, and $(n, m) = (2, 3)$ (see [BlockLCM/Three.lean](BlockLCM/Three.lean)). $\square$

## Length four

**The big idea.** Among four consecutive integers $n+1, n+2, n+3, n+4$, one is divisible by $4$ and another is $2 \pmod 4$, so the product always exceeds the LCM by a factor of $2$ at the prime $2$. At the prime $3$, two entries are multiples of $3$ if and only if $n+1$ and $n+4$ are divisible by $3$ (i.e., $n \equiv 2 \pmod 3$), adding an extra factor of $3$. No prime $\ge 5$ can divide two integers separated by at most $3$. Hence
$$(n+1)(n+2)(n+3)(n+4) = \begin{cases} 6\, M(n, 4) & \text{if } n \equiv 2 \pmod 3, \\ 2\, M(n, 4) & \text{otherwise.} \end{cases}$$
Because the product strictly increases with $n$, a collision $M(n, 4) = M(m, 4)$ with $n < m$ requires $n \not\equiv 2 \pmod 3$, $m \equiv 2 \pmod 3$, and the later product to be exactly **three times** the earlier one.

### Step 1: Collapse to a Pell-type equation

Pair the outer and inner factors of the 4-term product: $(n+1)(n+4) = n^2 + 5n + 4$ and $(n+2)(n+3) = n^2 + 5n + 6$. Setting $s(n) = n^2 + 5n + 5$, the product is simply $s(n)^2 - 1$, and completing the square gives $4s(n) + 5 = (2n + 5)^2$. Putting $x = s(m)$ and $y = s(n)$, the ratio equation $s(m)^2 - 1 = 3(s(n)^2 - 1)$ becomes the simultaneous Pell and square system
$$
x^2 - 3y^2 = -2, \qquad 4x + 5 = (2m + 5)^2, \qquad 4y + 5 = (2n + 5)^2,
$$
together with the residue constraints $x \equiv 1 \pmod 3$ (from $m \equiv 2 \pmod 3$) and $y \equiv 2 \pmod 3$ (from $n \not\equiv 2 \pmod 3$).

### Step 2: Congruence and Jacobi-symbol sieve

By descent, every positive integer solution of $x^2 - 3y^2 = -2$ is generated by the fundamental unit $2 + \sqrt{3}$:
$$x + y\sqrt{3} = (1 + \sqrt{3})(2 + \sqrt{3})^k, \qquad k \ge 0.$$

1. **Mod-39 filter:** Modulo $39$, the pairs $(x, y)$ are periodic with period $12$ in $k$. The conditions modulo $3$ eliminate all classes except $k \equiv 2$ or $8 \pmod{12}$. At $k \equiv 8 \pmod{12}$, we get $4x + 5 \equiv 7 \pmod{13}$, which is not a square modulo $13$. Hence $k \equiv 2 \pmod{12}$.
2. **Killing all $k > 2$ via a Lucas divisor:** Suppose $k \ne 2$. Since $12 \mid (k - 2)$, we may write $k = 2 + 2 \cdot 2^t j$ with $j$ odd and $t \ge 1$. Let $u_t$ be the rational part of $(2 + \sqrt{3})^{2^t}$, so $u_1 = 7$ and $u_{t+1} = 2u_t^2 - 1$. Modulo $156$, this sequence is $7, 97, 97, 97, \ldots$, so $u_t$ is always $7$ or $97 \pmod{156}$.

   Because $(2 + \sqrt{3})^{2^t} = u_t + v_t\sqrt{3}$ has norm $1$, squaring it gives $(2 + \sqrt{3})^{2\cdot 2^t} = (2u_t^2 - 1) + 2u_t v_t\sqrt{3} \equiv -1 \pmod{u_t}$. Raising to the odd power $j$ preserves the sign, so $u_t$ divides $(2 + \sqrt{3})^{2 \cdot 2^t j} + 1$. Multiplying by the $k = 2$ value $(1 + \sqrt{3})(2 + \sqrt{3})^2 = 19 + 11\sqrt{3}$ gives
   $$
   x + y\sqrt{3} \equiv -(19 + 11\sqrt{3}) \pmod{u_t}, \qquad 4y + 5 \equiv -39 \pmod{u_t}.
   $$
   For both residue classes $u_t \equiv 7, 97 \pmod{156}$, the Jacobi symbol $(-39 \mid u_t)$ equals $-1$, proving that $4y + 5$ cannot be a square!

Thus $k = 2$ is forced, giving $(x, y) = (19, 11)$ and $(n, m) = (1, 2)$ (see [BlockLCM/Four.lean](BlockLCM/Four.lean)). $\square$

> **A near-miss at $k = 3$:** The product equation alone actually has a second positive solution at $k = 3$: $7 \cdot 8 \cdot 9 \cdot 10 = 3 \cdot (5 \cdot 6 \cdot 7 \cdot 8)$ ($5040 = 3 \cdot 1680$). However, their LCMs are $2520$ and $840$ — the residue conditions modulo $3$ rule this solution out.

## Verification

With Elan installed, run the following commands in the project directory:

```sh
lake exe cache get
lake build
printf '%s\n' 'import BlockLCM' '#print axioms Erdos677.three_collision_iff' '#print axioms Erdos677.four_collision_iff' | lake env lean --stdin
```

Both theorems depend only on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
