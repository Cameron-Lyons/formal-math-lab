# Width-12 snake polyominoes — OEIS A397153 conjecture

**Research target; no proof or Lean project is supplied here.**

Let `s(n)` be the maximum number of cells in a snake polyomino contained
in a `12 × n` rectangle: equivalently, the maximum number of vertices in
an induced path in its grid graph. The conjectured recurrence is

```text
s(n + 6) = s(n) + 44    for n ≥ 13.
```

It follows from the conjectured generating function in
[OEIS A397153](https://oeis.org/A397153), attributed to Alain Goupil.
Related terms are *longest induced path in a width-12 grid*, *maximum snake
area*, and column 12 of [OEIS A360917](https://oeis.org/A360917).

Blondin Massé and Goupil's
[*Snake Polyominoes of Maximal Area in a Rectangle*](https://arxiv.org/abs/2606.13155)
does not prove this width-12 recurrence. The
[dated audit](../PRIOR_ART.md#width-12-grid-snakes-no-local-proof)
records the source checks and the limitation on accessing live OEIS text.
