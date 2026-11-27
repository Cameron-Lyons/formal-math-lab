# Manabe’s subtraction game with moves 3, 8, and 11k+1

For every integer $k\ge1$, the **only heap with Grundy value 3 has size $11k+4$**. The least preperiod is $11k+5$, and $11k+4$ is a period from that heap onward. This proves Manabe’s prediction of a positive preperiod for the entire residue class $1\bmod 11$ with base moves 3 and 8. [Manabe, Example 1](https://arxiv.org/html/2609.05358v2#S1)

For example, when $k=1$ the allowed moves are 3, 8, and 12. Starting at the empty heap, the first 16 values are `0001110021102213`. From heap 16 onward the five digits `00211` repeat.

## Proof

Write $p=11k+4$, so the moves are $3,8,p-3$. Let $A(r)$ be digit $r$ of the repeating string `00011100211`, counting from zero. Two rows describe the whole game.

| Heaps | Values |
| --- | --- |
| $0$ through $p$ | Read $A(0),\ldots,A(p)$. Put a 2 at $p-3$ and $p-2$, and a 3 at $p$. |
| From $p+1$ onward | Repeat $A(1),\ldots,A(p)$, putting a 2 at positions $3$ and $p-2$ in each copy. Positions in a copy run from 1 to $p$. |

At heap $p$ the three moves lead to $p-3$, $p-8$, and $3$. Their values are **2, 0, and 1**, so the smallest missing value is **3**. Every other entry in the two rows is 0, 1, or 2.

To verify the rows, substitute them into the rule that each heap takes the smallest value missing from its legal moves. Lean checks this directly for $0\le n<3p$ using comparisons and residues modulo 11, with $k$ arbitrary. In particular, the $p-3$ entries beginning at $p+1$ agree with those one row later. The largest move is $p-3$, so these entries determine the next one, then the next, and hence the entire tail. A period starting any earlier would repeat the unique 3. [Lean proof](ResidueOne.lean)

<details>
<summary>Checking the recurrence by hand</summary>

Write $E=\texttt{00211}$ and also use $A$ for the eleven-letter word above. The repeating tail is $EEA^{k-1}E$. Extend it periodically to the left and call the result $H$. A move of $p-3$ in this periodic word reads the same digit as moving *forward* three places.

In any concatenation of these tiles extending in both directions, the eight digits before a tile are `x1100211` with $x\in\{1,2\}$. The three digits after it are `00y` with $y\in\{0,2\}$. The table gives the neighbors seen at each position of a tile.

| Tile | Three places back | Three places forward | Eight places back |
| --- | --- | --- | --- |
| `00011100211` | `21100011100` | `1110021100y` | `x1100211000` |
| `00211` | `21100` | `1100y` | `x1100` |

At each position, its digit is the smallest value missing from the first two neighbors, and the third neighbor differs from that digit. Thus $H$ obeys the three-move rule wherever all moves are legal.

Put $d=p-3$. Before heap $d$, only moves 3 and 8 can be legal. The first eight values are `00011100` by inspection. After that the all-$A$ word obeys the two-move rule by the same table, since shifts of $-8$ and $+3$ agree modulo 11.

The proposed values differ from $H$ at just four heaps. At $0,3,d,p$ replace $1,2,0,1$ by $0,1,2,3$, respectively. For $n\ge d$ the rule therefore needs checking only when $n$ or one of its three followers is a changed heap. The seven possible checks are below. The middle column lists the values after removing $3,8,d$ stones, in that order.

| Heap | Follower values | Smallest missing |
| --- | --- | --- |
| $d$ | $1,1,0$ | 2 |
| $p$ | $2,0,1$ | 3 |
| $p+3$ | $3,1,0$ | 2 |
| $p+5$ | $0,2,2$ | 1 |
| $p+8$ | $1,3,0$ | 2 |
| $2p-6$ | $0,0,2$ | 1 |
| $2p-3$ | $1,1,3$ | 0 |

This verifies the two rows at every heap for every $k\ge1$.

</details>

## Verification

Run from this directory with Lean 4.36.0 and the neighboring `manabe-residue-seven` directory present.

```sh
lake --wfail build
lake env leanchecker --fresh ResidueOne
```

The main theorems are `SubtractionGame.ResidueOne.grundy_eq_three_iff` and `SubtractionGame.ResidueOne.periodic_from_iff`. Both use kernel-checked proofs and the standard library. The optional comparison proves the singleton theorem for `SubGame.grundy3` from Manabe’s own ancillary files. [Comparison and reproduction commands](ManabeBridge.lean) · [Prior-art check](../PRIOR_ART.md#manabes-subtraction-game-at-residue-one)
