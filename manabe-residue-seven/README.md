# A subtraction game with exactly one 3

Fix an integer `k ≥ 1`. From a heap of size `n`, a player may remove 3, 8,
or `11k+7` tokens if enough remain. The Grundy value is 3 exactly when
`n = 11k+10`. This proves the positive preperiod predicted in Manabe’s
Example 1 for the residue 7 modulo 11. [Original problem](https://arxiv.org/html/2609.05358v2#S1) · [Prior-art audit](../PRIOR_ART.md#manabes-subtraction-game)

Write `A = 00011100211`, `B = 00011102213`, and `D = 0021100211`.
Starting at heap zero, the sequence is `Aᵏ B` followed by `D Aᵏ` repeated
forever. The only 3 is the last digit of `B`. The least preperiod is
`11k+11` and the least eventual period is `11k+10`.
[Sequence and period theorems](UniqueThree.lean)

Run the following in this directory with Lean 4.36.0 to check
`SubtractionGame.grundy_eq_three_iff` and its corollaries.

```sh
lake build
```

The proof uses the Lean standard library. An optional comparison proves the
same theorem for the Grundy function in Manabe’s own Lean sources. The
comparison file includes commands to fetch those sources and check
`SubtractionGame.manabe_eq_three_iff`. [Comparison with Manabe’s definition](ManabeBridge.lean)
