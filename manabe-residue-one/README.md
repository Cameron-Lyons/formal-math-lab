# Manabe’s subtraction game with moves 3, 8, and $11k+1$

In an impartial **subtraction game**, two players take turns removing a legal number of stones from a single heap, and the last player able to move wins. Every heap size $n \ge 0$ has a **Grundy value** (or *nim-value*) $g(n)$: the smallest nonnegative integer *missing* from the Grundy values of the heaps reachable in one move (with $g(n) = 0$ marking a losing position). Because only finitely many moves are allowed, the sequence $g(0), g(1), g(2), \ldots$ always becomes periodic eventually — after some initial **preperiod** of non-repeating values.

For the move set $\{3, 8, 11k + 1\}$ (with any integer $k \ge 1$), we prove in Lean 4 that the **only heap with Grundy value 3 has size $11k + 4$**. Consequently, the sequence is never purely periodic: its least preperiod is $11k + 5$, and $11k + 4$ is a period from heap $11k + 5$ onward. This proves Manabe’s prediction of a positive preperiod for the entire residue class $1 \bmod 11$ with base moves $3$ and $8$ ([Manabe, Example 1](https://arxiv.org/html/2609.05358v2#S1)).

**Concrete example ($k = 1$):** The legal moves are $3$, $8$, and $12$. Starting at the empty heap $n = 0$, the first $16$ Grundy values (heaps $0$ through $15$) are `0001110021102213` — notice the lone `3` at heap $15 = 11(1) + 4$. From heap $16$ onward, the five-digit block `00211` repeats forever (so $15 = 3 \times 5$ is a period).

| Field | Summary |
| --- | --- |
| Problem | Manabe’s subtraction game with move set $\{3, 8, 11k + 1\}$ ($k \ge 1$), `arXiv:2609.05358v2` Example 1 (residue $1 \bmod 11$) |
| Status | Proved in Lean 4 for all $k \ge 1$. |
| Main theorems | `SubtractionGame.ResidueOne.grundy_eq_three_iff` and `SubtractionGame.ResidueOne.periodic_from_iff` in [ResidueOne.lean](ResidueOne.lean) |
| Verification | `lake --wfail build && lake env leanchecker --fresh ResidueOne` (Lean 4.36.0, stdlib only; pure kernel proofs) |
| Prior art | |

## How the proof works

Write $p = 11k + 4$, so the three legal moves are $3$, $8$, and $p - 3$. Let $A(r)$ denote digit $r$ (counting from zero, modulo $11$) of the repeating $11$-digit base word `00011100211` — which is the purely periodic Grundy sequence of the simpler two-move game $\{3, 8\}$.

**The big idea:** Adding the large third move $p - 3$ perturbs the base pattern $A^\infty$ at only a handful of heaps, producing a single `3` at heap $p$ and then locking into a repeating cycle of length $p$. Two rows completely specify the Grundy values for every heap $n \ge 0$:

| Heaps | Values |
| --- | --- |
| $0$ through $p$ | Read $A(0), \ldots, A(p)$. Put a `2` at $p - 3$ and $p - 2$, and a `3` at $p$. |
| From $p + 1$ onward | Repeat $A(1), \ldots, A(p)$, putting a `2` at positions $3$ and $p - 2$ in each copy. Positions in a copy run from $1$ to $p$. |

At heap $p$, the three legal moves lead to $p - 3$, $p - 8$, and $3$. Their values are **2, 0, and 1**, so the smallest missing value is **3**. Every other entry in both rows is $0$, $1$, or $2$.

**Why checking a finite prefix proves periodicity forever:** To verify the two-row formula, we plug it into the Grundy recurrence (each heap takes the smallest nonnegative integer missing from its legal moves). Lean checks this directly for $0 \le n < 3p$ using comparisons and residues modulo $11$, uniformly for arbitrary $k \ge 1$.

In particular, the $p - 3$ consecutive entries starting at heap $p + 1$ match those starting one period later (at $2p + 1$). Because the largest legal move is $p - 3$, every heap's Grundy value is determined solely by the preceding $p - 3$ values — so once two windows of width $p - 3$ agree, the next value must match, then the next, locking the entire tail into period $p$ forever. Finally, no period can start earlier than $p + 1$, because it would have to repeat the unique `3` at heap $p$. [Lean proof](ResidueOne.lean)

<details>
<summary>Checking the recurrence by hand</summary>

Write $E = \texttt{00211}$ and reuse $A$ for the eleven-letter word `00011100211`. The repeating tail block of length $p = 11k + 4$ is $E E A^{k-1} E$ (length $5 + 5 + 11(k-1) + 5 = 11k + 4$). Extend this block periodically to the left as well, and call the bi-infinite periodic sequence $H$. Inside $H$, stepping back by $p - 3$ reads the exact same digit as stepping *forward* three places.

In any bi-infinite concatenation of the tiles $A$ and $E$, the eight digits immediately before a tile are `x1100211` with $x \in \{1, 2\}$, and the three digits immediately after it are `00y` with $y \in \{0, 2\}$. The table lists the three neighbors seen from each position of a tile:

| Tile | Three places back | Three places forward | Eight places back |
| --- | --- | --- | --- |
| `00011100211` | `21100011100` | `1110021100y` | `x1100211000` |
| `00211` | `21100` | `1100y` | `x1100` |

At every position, the tile's digit is the smallest nonnegative integer missing from its first two neighbors, and the third neighbor differs from that digit. Thus $H$ obeys the three-move Grundy rule wherever all three moves are legal.

Now put $d = p - 3$. Before heap $d$, only moves $3$ and $8$ can be legal. The first eight values are `00011100` by inspection; after that, the all-$A$ word obeys the two-move rule by the same table, because shifts of $-8$ and $+3$ agree modulo $11$.

Our proposed two-row sequence differs from $H$ at just four heaps: at $0, 3, d, p$, the digits $1, 2, 0, 1$ of $H$ are replaced by $0, 1, 2, 3$, respectively. For $n \ge d$, the three-move rule therefore only needs checking when $n$ itself or one of its three followers ($n - 3$, $n - 8$, $n - d$) is one of those four changed heaps. All seven resulting checks are listed below (with the middle column giving the values after removing $3, 8, d$ stones, in that order):

| Heap | Follower values | Smallest missing |
| --- | --- | --- |
| $d$ | $1, 1, 0$ | $2$ |
| $p$ | $2, 0, 1$ | $3$ |
| $p + 3$ | $3, 1, 0$ | $2$ |
| $p + 5$ | $0, 2, 2$ | $1$ |
| $p + 8$ | $1, 3, 0$ | $2$ |
| $2p - 6$ | $0, 0, 2$ | $1$ |
| $2p - 3$ | $1, 1, 3$ | $0$ |

This verifies the two-row formula at every heap for every $k \ge 1$.

</details>

## Verification

Run from this directory with Lean 4.36.0 and the neighboring `manabe-residue-seven` directory present:

```sh
lake --wfail build
lake env leanchecker --fresh ResidueOne
```

The main theorems are `SubtractionGame.ResidueOne.grundy_eq_three_iff` and `SubtractionGame.ResidueOne.periodic_from_iff`. Both use kernel-checked proofs and the standard library.
