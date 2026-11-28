# Reciprocal Rado numbers $f_2(k) = 3k^2$ for all even $k \ge 4$

Pick any even integer $k \ge 4$, and color the integers $\{1, 2, \ldots, N\}$ red and blue. How large must $N$ be to guarantee a single-color solution (repeated denominators allowed) to the $k$-term unit-fraction equation

$$
\frac{1}{x_1} + \frac{1}{x_2} + \cdots + \frac{1}{x_k} = \frac{1}{y}?
$$

In Ramsey theory, this exact threshold is the two-color **reciprocal Rado number** $f_2(k)$. Here we prove in Lean 4 that for **every even $k \ge 4$** and every $N \in \mathbb{N}$, every red-blue coloring of $\{1, 2, \ldots, N\}$ contains a monochromatic solution if and only if $N \ge 3k^2$.

This proves the complete even half of Gaiser and Ramezanpour's Conjecture 1.3 (`arXiv:2607.04373v1`) — which asks whether $f_2(k) = 3k^2$ for all $k \ge 4$ that are not odd prime powers — and settles Arevalo's Conjecture B (`farev/Matematica`), extending Gaiser and Ramezanpour's Theorem 3.3 ($k = 3 \cdot 2^m$) to **every even $k \ge 4$**.

| Field | Summary |
| --- | --- |
| Problem | Two-color reciprocal Rado numbers $f_2(k) = 3k^2$ for all even $k \ge 4$ (Gaiser–Ramezanpour `arXiv:2607.04373v1` Conjecture 1.3, even case; Arevalo Conjecture B) |
| Status | Proved in full for all even $k \ge 4$ in pure Lean 4. The odd non-prime-power case remains open in general. A separate certificate settles $k=33$. [33-term proof](../k33/) |
| Main theorem | `EvenUnitFractions.forces_iff {k : Nat} (heven : k % 2 = 0) (hk : 4 ≤ k) (N : Nat) : Forces k N ↔ 3 * k * k ≤ N` in [EvenUnitFractions.lean](EvenUnitFractions.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; pure kernel proof, no `sorry`, no `native_decide`, standard axioms only) |
| Prior art | Checked 26 November 2026: Gaiser and Ramezanpour proved $k = 3 \cdot 2^m$ and computed $k \le 25$; Arevalo certified through $k = 8$ and left all even $k \ge 4$ as Conjecture B; this repository previously settled $k = 26$ and $k = 28$. No earlier proof covering all even $k \ge 4$ was found. |

## How the proof works

### Lower bound ($f_2(k) \ge 3k^2$ for all $k \ge 3$)

Implemented in [EvenUnitFractions/Lower.lean](EvenUnitFractions/Lower.lean), this generalizes Gaiser and Ramezanpour's Theorem 1.1 avoiding coloring (which works for *all* $k \ge 3$, even or odd). Paint $\{1, \ldots, 3k^2 - 1\}$ in two bands:

* **Red:** $\{3, \ldots, 3k - 1\}$.
* **Blue:** $\{1, 2\} \cup \{3k, \ldots, 3k^2 - 1\}$.

Notice that any monochromatic solution whose summands are all $\le M$ satisfies $1/y = \sum_{i=1}^k 1/x_i \ge k/M$, hence $ky \le M$.

* **No red solution:** Setting $M = 3k - 1$ gives $ky \le 3k - 1$, forcing $y \le 2$ — contradicting $y \ge 3$.
* **No blue solution:** Setting $M = 3k^2 - 1$ gives $ky \le 3k^2 - 1$, so $y \le 3k - 1$, leaving only $y \in \{1, 2\}$ among blue integers. Doubling the equation produces $2/y \in \{1, 2\}$ (an integer $\le 2$). Meanwhile, all summands with denominators $\ge 3k$ together contribute at most $k \cdot \frac{2}{3k} = \frac{2}{3} < 1$, which cannot bridge the gap to an integer — so none of them can appear. That forces all $k$ summands into $\{1, 2\}$, whose doubled sum is at least $k \ge 3 > 2$, contradiction.

### Upper bound ($f_2(k) \le 3k^2$ for all even $k \ge 4$)

Implemented in [EvenUnitFractions/Upper.lean](EvenUnitFractions/Upper.lean). Suppose a red-blue coloring $c$ of $\{1, \ldots, 3k^2\}$ avoids monochromatic solutions.

**The big idea:** Write $k = 2s$ ($s \ge 2$). By the **opposites rule** ($1/d = k/(kd)$), $c(kd) = \neg c(d)$ for every $1 \le d \le 3k$. We split on the colors of the tiny integers $1, 2, 3, 4$ (up to swapping red and blue):

* **Quick cases (Cases 1 and 2):** If $2$ and $3$ have opposite colors, or if $1, 2, 3$ match while $4$ disagrees, two explicit identities close the case immediately.
* **Deep cases (Cases 3 and 4):** Otherwise $2, 3, 4$ all share a color $\mathrm{col}$ (in Case 4, a one-line identity forces $c(4) = \mathrm{B}$ for $k \ge 6$). We then climb a **dyadic ladder** (`ladder`) — repeatedly doubling $(2q, 3q, 4q) \mapsto (6q, 8q)$ — until we land on the unique power of two $p = 2^m$ ($m \ge 1$) bracketing $k$ via $2p \le k < 4p$. That hands us three monochromatic denominators $2p, 3p, 4p$ right at the scale of $k$, where simple linear combinations finish both cases. (For instance, at $k = 26$ we get $p = 8$, and Case 3's binary split below becomes $1 = \frac{6}{16} + \frac{20}{32}$.)

Below is the complete case breakdown (writing $m/d$ for $m$ copies of $1/d$):

1. **Case 1 ($c(2) \ne c(3)$):** WLOG $c(2) = \mathrm{R}$ and $c(3) = \mathrm{B}$. By the opposites rule, $c(2k) = c(3k^2) = \mathrm{B}$ and $c(3k) = \mathrm{R}$. The identity

   $$
   \frac{1}{2} = \frac{s}{3k} + \frac{s}{3s}
   $$

   has $2$ and $3k$ red, so it forces $c(3s) = \mathrm{B}$, making $\frac{1}{3} = \frac{s-1}{3s} + \frac{1}{2k} + \frac{s}{3k^2}$ monochromatic blue.

2. **Case 2 ($c(1) = c(2) = c(3) = \mathrm{R},\ c(4) = \mathrm{B}$):** For $k = 4$, $1 = 2/3 + 2/6$ forces $c(6) = \mathrm{B}$, hence $c(16) = c(24) = \mathrm{R}$, making $1/2 = 1/3 + 2/16 + 1/24$ all red. For even $k \ge 6$,

   $$
   1 = \frac{2}{3} + \frac{k-2}{3(k-2)}, \qquad 1 = \frac{1}{2} + \frac{1}{3} + \frac{k-2}{6(k-2)}
   $$

   force $3(k-2)$ and $6(k-2)$ blue, making $\frac{1}{4} = \frac{s-3}{3(k-2)} + \frac{s+3}{6(k-2)}$ monochromatic blue.

3. **Shared dyadic ladder (`ladder`):** For any even $k \ge 6$, if $c(2) = c(3) = c(4) = \mathrm{col}$, Gaiser and Ramezanpour's six-identity induction step $(2q, 3q, 4q) \mapsto (6q, 8q)$ requires only $2 \mid k$ and $4q \le k$. Iterating to the unique $p = 2^m$ ($m \ge 1$) with $2p \le k < 4p$ gives

   $$
   c(2p) = c(3p) = c(4p) = \mathrm{col}.
   $$

4. **Case 3 ($c(1) = c(2) = c(3) = c(4) = \mathrm{R}$):** For $k = 4$, $1 = 4/4$ immediately contradicts avoidance. For even $k \ge 6$, the ladder gives $c(2p) = c(4p) = \mathrm{R}$, and the binary-splitting identity

   $$
   1 = \frac{4p - k}{2p} + \frac{2(k - 2p)}{4p}
   $$

   is monochromatic red.

5. **Case 4 ($c(1) = \mathrm{R},\ c(2) = c(3) = \mathrm{B}$):** By the opposites rule, $c(k) = c(2k^2) = c(3k^2) = \mathrm{B}$ and $c(2k) = c(3k) = \mathrm{R}$. The identity

   $$
   \frac{1}{k} = \frac{1}{3s} + \frac{2}{2k^2} + \frac{k-3}{3k^2}
   $$

   forces $c(3s) = \mathrm{R}$ for every even $k \ge 4$.
   * For $k = 4$, $c(6) = \mathrm{R} \implies c(24) = \mathrm{B}$, making $1/3 = 1/4 + 1/24 + 2/48$ all blue (using $c(4) = \mathrm{B}$, since $1 = 4/4$ rules out $c(4) = \mathrm{R}$).
   * For even $k \ge 6$, we force $c(4) = \mathrm{B}$ in one line: if $c(4) = \mathrm{R}$, then $1 = 3/4 + 3/12$ (for $k = 6$) or

     $$
     1 = \frac{2}{4} + \frac{6}{3s} + \frac{k - 8}{2k} \qquad (k \ge 8)
     $$

     is monochromatic red.
   * Applying the ladder with $\mathrm{col} = \mathrm{B}$ gives $c(2p) = c(3p) = c(4p) = \mathrm{B}$, hence $c(3pk) = c(4pk) = \mathrm{R}$.
     * **Subcase $3k \le 8p$:** The identity

       $$
       \frac{1}{3s} = \frac{8p - 3k}{3pk} + \frac{4k - 8p}{4pk}
       $$

       is monochromatic red.
     * **Subcase $3k > 8p$** (so $k \le 4p - 2$ and $5s + 2 > 6p$): The two blue identities $1/(2p) = 1/(4p) + (k-1)/(4p(k-1))$ and $1/(2p) = 1/(3p) + (k-1)/(6p(k-1))$ force $4p(k-1)$ and $6p(k-1)$ red (both $\le 3k^2$), and

       $$
       \frac{1}{3s} = \frac{2p - s}{3pk} + \frac{4p - k - 2}{4p(k - 1)} + \frac{5s - 6p + 2}{6p(k - 1)}
       $$

       is monochromatic red.

## Check the proof

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```
