# At least 32,155,680 three-color T boards

There are at least **32,155,680 distinct valid labeled boards**. The certificate contains **2,679,640 disjoint orbits**, each of size 12 under color permutation and horizontal reflection. This raises the previous bound of 21,158,736 by **10,996,944**. [Lean theorem](SpliceNextCertificates.lean) · [Previous lower bound](SPLICE_FURTHER.md)

| Source | Groups | Orbit representatives | Labeled boards |
|---|---:|---:|---:|
| Earlier certificate | 310 | 1,763,228 | 21,158,736 |
| Eight new four-cap prefixes | 8 | 70,400 | 844,800 |
| Continuations of earlier searches | 6 | 176,552 | 2,118,624 |
| Prefixes found by rebuilding upper rows | 5 | 184,231 | 2,210,772 |
| Ten new pivots sharing the same six caps | 10 | 460,854 | 5,530,248 |
| Groups found using caps with one occurrence of color 2 | 2 | 24,375 | 292,500 |
| **Total** | **341** | **2,679,640** | **32,155,680** |

## A family of pivots with six interchangeable caps

A valid board uses every ordered quadruple of three colors once at its 81 T placements. Write the top five rows as a *cap*, the next row of eleven cells as the *pivot*, and the last four rows as a *tail*. There are 25 placements in the cap and pivot and 56 in the pivot and tail. Whenever those two sets of patterns are complementary, the cap and tail fit together. [Splice theorem](Splice.lean)

The six caps used here all have the same 16 patterns within their five rows. Their bottom rows are `010000221` and `100000221`, which differ by exchanging the first two cells. If a pivot begins with four identical digits, its first two triples are equal. Exchanging the first two cap cells swaps the corresponding two T patterns and leaves the other seven crossing patterns unchanged. For example, under a pivot beginning with `2222`, the two patterns are `0222` and `1222`. Thus all six caps give the same 25 patterns whenever the nine crossing patterns are distinct and disjoint from the internal 16.

The following ten pivots pass that test and have the indicated numbers of recorded tails. Any of the six caps fits any tail in the corresponding row. This gives **6 × 76,809 × 12 = 5,530,248 labeled boards**. [Explicit caps, pivots and tails](splice_next.json)

| Pivot | Tails used |
|---|---:|
| `22221220022` | 12,500 |
| `22221102022` | 12,500 |
| `22221202022` | 10,999 |
| `22221202002` | 6,410 |
| `22221120022` | 3,500 |
| `11112212002` | 2,488 |
| `22220212122` | 6,977 |
| `22221211022` | 6,610 |
| `22221102122` | 7,928 |
| `22221101122` | 6,897 |

## Fifteen interchangeable caps

The pivot `20121212001` admits 15 different caps with the same 25 upper patterns. Every cap contains thirteen cells of color 0, eleven of color 1, and one of color 2. Thirteen caps have the same internal set of 16 patterns. Each of the other two has a different internal set, but its nine placements crossing into the pivot supply exactly the patterns it needs. With **1,419 recorded tails**, this one pivot gives **15 × 1,419 × 12 = 255,420 labeled boards**. The largest group in the previous certificate had 12 caps.

A second pivot, `01021212102`, also admits 15 caps. Its 206 recorded tails give a further 37,080 labeled boards.

To find these families, the search enumerated five-row caps with one cell of color 2, grouped them by their internal patterns, and tested which last rows give the same crossing patterns at a fixed pivot. A reverse enumeration using all 25 patterns recovered the full cap lists. Both cap lists and all their tails are recorded and checked in Lean. [New witnesses](splice_next.json)

The following search recovers the cap families directly from their pivots. It enumerates caps containing a single 2 and groups them by all 25 upper patterns. At `20121212001`, 19,347 caps give 17,349 different pattern sets. Exactly one set occurs on at least fifteen caps. [Cap search](find_rare_caps.py)

```sh
python find_rare_caps.py 20121212001
python find_rare_caps.py 01021212102
```

## Extending a search past its previous cutoff

Six older prefixes each stopped after 3,500 tails. The new searches resumed immediately after the last recorded tail, in lexicographic order, and exhausted the rest of each prefix. They found 44,138 additional tails for four caps apiece. The largest continuation has 13,684 tails and contributes 656,832 labeled boards by itself. [Search implementation](splice_search.cpp) · [Earlier tail lists](splice_further.json)

Every board determines its pivot, the set of patterns above it, and its tail. Groups with different pivots or upper pattern sets are disjoint. For the six repeated groups, Lean checks that the greatest earlier tail code is strictly less than the least later one. All tails have the same length, so sorting by base-three code agrees with sorting their digit strings. To distinguish the twelve symmetry images, the proof reads the transformed cap and pivot, identifies the operation from the six upper rows, and inverts it. [Tail interval proof](SpliceRanges.lean) · [Symmetry proof](SplicePrefixSymmetry.lean)

Other new prefixes were found by fixing lower rows of an existing board and rebuilding its upper rows with the remaining patterns. One such prefix, with pivot `00110011002`, has 12 caps and 3,561 tails. Its contribution is 512,784 labeled boards. Each group contributes only its explicit cap–tail products. The unrestricted count remains unknown.

## Reproducing the checks

Run these commands from the proof directory to regenerate the new Lean sources, check the combined theorem, and expand every labeled board independently.

```sh
python prepare_splice_next.py
lake build SpliceNextCertificates
python verify_splice.py --through-next --expand --jobs 3
```

The expanded checker constructs every symmetry image, evaluates its 81 Cartesian T placements, and checks for duplicate full 100-digit boards using exact base-three encodings. It also checks inclusion of the original 17,160-board family. The theorem uses the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. [Independent checker](verify_splice.py) · [Expanded audit](splice-next-audit.log) · [Lean build log](splice-next-lean-build.log)

The discovery replay accepts one-based group numbers. The command below exhausted continuation group 9 and reproduced its four caps and 5,411 new tails. Omitting group numbers replays all new groups with their recorded bounds.

```sh
python reproduce_splice.py --certificate splice_next.json --exhaust 9
```
