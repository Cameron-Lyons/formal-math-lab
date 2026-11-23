# Nonattacking kings with k per row and column — Lean proof of the Parks theorem

**This formalizes an existing theorem.** Minevich, Cunningham, Karan, and
Gyllinsky proved the more general rectangular result in *Parks: A Doubly
Infinite Family of NP-Complete Puzzles and Generalizations of A002464*
(2024), [Theorem 3](https://arxiv.org/html/2411.02251v1#S7.Thmtheorem3).
Set both quotas to `k` to obtain the square case here.

## Exact statements

Place nonattacking kings on an `n × n` board, with exactly `k` kings in
each row and column. Adjacent squares, including diagonals, attack.

- For `n ≥ 2` and `k ≥ 1`, **`n ≥ 4k`**:
  [`Kings.lowerBound`](Spacing.lean).
- For `k > 0`, precisely **two labeled placements** exist at `n = 4k`:
  [`Kings.exactlyTwo`](Kings.lean). Coordinates are fixed; arrangements
  are not identified by symmetry.

The `1 × 1` one-king board is excluded from the minimum-size statement.
Definitions are in [Board.lean](Board.lean), constructions in
[Constructions.lean](Constructions.lean), and a proof outline in
[Kings.lean](Kings.lean).

## Reproduce

```sh
lake build
```

The project pins Lean 4.36.0 and uses only the standard library.

## Related terminology

Search identifiers include [OEIS A387098](https://oeis.org/A387098),
[A389766](https://oeis.org/A389766), A002464, *generalized Hertzsprung problem*,
*Parks puzzle*, and *Shuriken arrangements*.

See the [collection audit](../PRIOR_ART.md#nonattacking-kings-existing-proof-found).
No earlier matching Lean formalization was located; formalization priority
is unconfirmed.
