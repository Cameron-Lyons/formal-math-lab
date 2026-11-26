# At least 32,155,680 three-color T boards

There are at least **32,155,680 distinct valid labeled boards**, forming **2,679,640 disjoint orbits** of size 12 under color permutation and horizontal reflection. This adds **10,996,944 boards** to the [previous lower bound](SPLICE_FURTHER.md) of 21,158,736, verified in [SpliceNextCertificates.lean](SpliceNextCertificates.lean).

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

A valid board uses every ordered quadruple of three colors once across its 81 T placements. Call the top five rows a *cap*, the eleven-cell sixth row the *pivot*, and the last four rows a *tail*. There are 25 placements in the cap and pivot and 56 in the pivot and tail; whenever those two pattern sets are complementary, the cap and tail fit together ([Splice.lean](Splice.lean)).

The six caps used here all share the same 16 internal patterns. Their bottom rows are `010000221` and `100000221`, differing only by swapping the first two cells. When a pivot starts with four identical digits, its first two triples match, so swapping those two cap cells just swaps the corresponding two T patterns and leaves the other seven crossing patterns untouched. For example, with a pivot starting in `2222`, those two patterns are `0222` and `1222`. As long as the nine crossing patterns are all distinct and disjoint from the 16 internal patterns, all six caps produce the exact same 25 upper patterns.

The ten pivots below pass that check, with their explicit caps, pivots, and tails recorded in [splice_next.json](splice_next.json). Every one of the six caps fits every tail in its row, giving **6 × 76,809 × 12 = 5,530,248 labeled boards**.

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

The pivot `20121212001` allows 15 different caps with the same 25 upper patterns. Each cap has thirteen 0s, eleven 1s, and a single 2. Thirteen of them share the same 16 internal patterns; the other two have different internal sets, but their nine crossing placements fill in the missing patterns. With **1,419 recorded tails**, this pivot alone yields **15 × 1,419 × 12 = 255,420 labeled boards** (up from a maximum of 12 caps per group in the previous certificate).

A second pivot, `01021212102`, also admits 15 caps. Its 206 recorded tails add 37,080 labeled boards.

To find these groups, we enumerated five-row caps containing a single 2, grouped them by their internal patterns, and checked which bottom rows produce the same crossing patterns for a fixed pivot. A reverse search using all 25 patterns then recovered the full cap lists, and all caps and tails are stored in [splice_next.json](splice_next.json) and checked in Lean.

You can reproduce both cap families directly from their pivots with [find_rare_caps.py](find_rare_caps.py), which enumerates single-2 caps and groups them by all 25 upper patterns. At `20121212001`, 19,347 caps produce 17,349 distinct pattern sets, and only one set appears on 15 or more caps:

```sh
python find_rare_caps.py 20121212001
python find_rare_caps.py 01021212102
```

## Extending a search past its previous cutoff

Six older prefixes in [splice_further.json](splice_further.json) stopped at 3,500 tails. Using [splice_search.cpp](splice_search.cpp), we resumed immediately after each last recorded tail in lexicographic order and exhausted the rest of all six prefixes, finding 44,138 more tails for four caps each. The largest continuation adds 13,684 tails, or 656,832 labeled boards on its own.

Every board fixes its pivot, upper pattern set, and tail. Groups with different pivots or upper pattern sets cannot overlap. For the six continued groups, [SpliceRanges.lean](SpliceRanges.lean) checks that the largest earlier tail code is strictly smaller than the smallest new tail code (all tails have the same length, so base-three order matches lexicographic order). To keep the twelve symmetry images separate, [SplicePrefixSymmetry.lean](SplicePrefixSymmetry.lean) reads the transformed six upper rows, identifies the symmetry, and inverts it.

Other new prefixes came from fixing the lower rows of an existing board and rebuilding the upper rows from the remaining patterns. One of them, at pivot `00110011002`, has 12 caps and 3,561 tails, adding 512,784 labeled boards. Each group only counts its explicit cap-tail products; the unrestricted total is still unknown.

## Reproducing the checks

Run these commands from the proof directory to regenerate the new Lean files, check the combined theorem, and independently expand every labeled board:

```sh
python prepare_splice_next.py
lake build SpliceNextCertificates
python verify_splice.py --through-next --expand --jobs 3
```

The [independent checker](verify_splice.py) builds every symmetry image, evaluates its 81 Cartesian T placements, checks for duplicate 100-digit boards using exact base-three encodings, and verifies that the original 17,160-board family is included (see the [expanded audit](splice-next-audit.log)). The theorem uses only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound` (see the [Lean build log](splice-next-lean-build.log)).

The discovery replay accepts one-based group numbers (omitting them replays all new groups up to their recorded bounds). For example, this command exhausts continuation group 9 and reproduces its four caps and 5,411 new tails:

```sh
python reproduce_splice.py --certificate splice_next.json --exhaust 9
```
