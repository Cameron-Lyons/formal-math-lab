# Five permutation-fair 30-sided dice

Can five independently rolled, fair 30-sided dice be labeled with 1 through 150 so that each of the 120 player orders is equally likely? The unrestricted question was open in the researchers’ records on 24 November 2026. [Go First Dice open questions](http://gofirstdice.ericharshbarger.org/doku.php?id=open_questions#d30)

## Results

- **Counting a labeling.** Write the owner of each face in increasing label order, using die numbers 0 through 4. A roll with order `[2, 0, 1, 4, 3]`, for example, picks one occurrence of each of those five numbers in that order. `FiveDice.check30_iff` proves that the checker accepts exactly the valid labelings with 202,500 such choices for every order. [FiveDice.lean](FiveDice.lean)
- **A necessary condition.** At a face of one die, count the higher labels on each of the four opponents. Each die must have a face where two of those counts differ modulo four. The theorem is `FiveDice.EqualCuts.needs_distinct_residues`. [EqualCuts.lean](EqualCuts.lean)
- **Mirrored blocks.** Fifteen blocks, each consisting of a permutation of the dice followed by its reverse, cannot produce a fair labeling. `FiveDice.Mirrored.no_fifteen_mirrored` gives a Lean proof of this known exclusion. The researchers’ exhaustive search also covers the broader column-grouped family. [MirroredObstruction.lean](MirroredObstruction.lean) · [Prior-art audit](../PRIOR_ART.md)
- **A verified example.** For Paul Meyer’s 60-sided dice, each order occurs 6,480,000 times. The same checker proves `FiveDice.meyer60_fair` by kernel reduction. [Meyer60.lean](Meyer60.lean) · [The Dice Lab](https://www.mathartfun.com/thedicelab.com/GFD5.html)

## Reproduce

Run `lake build` in this directory with Lean 4.36.0. The project uses Lean’s standard library. The mirrored-block proof uses `native_decide` for 5,400 finite inequalities.
