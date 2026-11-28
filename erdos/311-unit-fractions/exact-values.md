# Exact gaps for 58 through 200

What does $\delta(N)$—the closest nonzero distance from $1$ to a sum of distinct unit fractions $\sum_{a \in A} 1/a$ with $A \subseteq \{1, \ldots, N\}$—actually look like for concrete values of $N$? Here we compute and independently certify the **exact** value of $\delta(N)$ and an explicit achieving subset $A$ for every integer $58 \le N \le 200$.

The data table records each maximal interval $u \le N \le v$ on which $\delta(N)$ stays constant, together with the signed fraction $\sum_{a \in A} 1/a - 1$ of the displayed witness. For instance, across $98 \le N \le 100$ the minimum is
$$
\delta(98) = \delta(99) = \delta(100)
= \frac{13914972457}{1415221188454793086396836206400}.
$$
The certified values agree with the earlier table through $60$ on the overlapping range $58 \le N \le 60$. [Exact fractions and denominators](exact_gaps.tsv) · [Earlier table through 60](https://github.com/arhancanli/quantavane-erdos-results/blob/main/311/results/table.md)

---

## Computation: split-and-meet search

Checking all $2^N$ subsets directly is impossible at $N = 200$. Instead, the search exploits the same smooth/rough split that powers the asymptotic theorems, paired with a meet-in-the-middle lookup modulo $M$.

Let $L = \operatorname{lcm}(1, \ldots, N)$, and choose a "smooth" divisor $D \mid L$, putting $M = L / D$. Partition the allowed denominators $\{2, \ldots, N\}$ into two groups (we can safely exclude denominator $1$: including $1$ gives either exact equality $1$ or a sum $\ge 1 + 1/N$, which has error at least $1/N$ and is easily beaten by the witnesses):

1. **First group (divisors of $D$):** Multiplying any denominator $d \mid D$ by $L$ gives $L/d = M \cdot (D/d)$, an integer multiple of $M$. Thus the entire first group only shifts the scaled numerator modulo $L$ by multiples of $M$—it never changes the residue modulo $M$!
2. **Second group (remaining denominators from $2$ to $N$):** Split these remaining denominators roughly in half into a left half and a right half. Enumerate all subset totals $x$ (left half) and $y$ (right half) in units of $1/L$.
   * For any pair $(x, y)$, the distance of $(x + y)$ to the nearest multiple of $M$ is a **lower bound** on $|L(\sum 1/a - 1)|$ (a zero residue modulo $M$ can only yield $0$ or a nonzero gap at least $M$).
   * Below $M/2$, only the single nearest multiple of $M$ can realize the gap.
   * Sorting the residues of $y \bmod M$ and scanning outward in both directions from $-x \bmod M$ visits candidate pairs in exact increasing order of distance! The very first positive distance below $M/2$ whose required first-group multiple of $M$ is feasible is guaranteed to be the exact minimum $\delta(N)$. The search then checks the witness using exact rational arithmetic.

### Deciding first-group feasibility

To test whether a target numerator over $D$ can be realized by the first group:
* Split off a modest **base** divisor of $D$, and precompute all attainable numerators over the base using an exact bitset subset sum.
* Move any denominator that exceeds the base exponent at *multiple* primes out of the first group into the second group during the initial split. Every remaining non-base first-group denominator then belongs to a unique prime block (the single prime where its exponent exceeds the base exponent).
* For each such prime, the target numerator over $D$ determines the exact residue required modulo the corresponding prime power in $D/\mathrm{base}$. The search iterates over matching totals in each prime block and looks up the remaining base target in the precomputed bitset. [Search](exact_gaps.py)

---

## Independent verification

To eliminate bugs or blind spots in the search code, a completely separate verification program certifies the entire table from scratch.

**Why two checks per row suffice.** For any table row covering $u \le N \le v$:
* **Upper bound ($\delta(N) \le \text{claimed}$ on $[u, v]$):** Exhibiting a valid witness subset $A \subseteq \{1, \ldots, u\}$ whose exact rational sum has the claimed signed error proves the upper bound for every $N \ge u$.
* **Lower bound ($\delta(N) \ge \text{claimed}$ on $[u, v]$):** Since available subsets only grow with $N$, ruling out every strictly smaller nonzero gap at the *right* endpoint $N = v$ proves the lower bound for every $N \le v$.

**How the independent checker rules out smaller gaps at $v$.**
1. It uses *all* divisors of its chosen $D$ in the first group, and splits the remaining denominators into left and right halves by alternating positions.
2. Around each left-half total, a strict residue window modulo $M$ extracts every left/right pair capable of beating the claimed gap.
3. For each surviving pair, it decides exact first-group feasibility by **recursive prime peeling** rather than prime-power blocks: pick a prime $p \mid D$; only denominators $d \mid D$ with $p \nmid (D/d)$ contribute modulo $p$ to the numerator over $D$. Enumerating subsets of those denominators that match the target modulo $p$, subtracting them, and dividing both the remaining target and $D$ by $p$ removes one prime factor of $p$ from $D$. When $D$ becomes small, an exact bitset closes the recursion.
4. In addition, the checker verifies that the table intervals are strictly ordered and contiguous across $58 \le N \le 200$, and checks every witness's signed error using exact rational arithmetic.

*Trust boundary:* The numerical workload heuristic used to pick $D$ affects only runtime, never the mathematical validity of an exclusion—every residue pair beating the claimed gap is exhaustively tested for the chosen $D$. [Checker](verify_exact.py)

---

## Reproduction commands

Run from the repository root with Python 3.10 or later:

~~~sh
python3 erdos/311-unit-fractions/verify_exact.py
python3 erdos/311-unit-fractions/exact_gaps.py 98 100
~~~

This certified table covers the finite range $58 \le N \le 200$; whether $-\log \delta(N)/N$ tends to a positive limit as $N \to \infty$ remains open.
