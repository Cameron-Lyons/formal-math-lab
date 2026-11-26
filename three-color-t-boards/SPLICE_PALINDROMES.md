# At least 45,083,592 three-color T boards

The certificate proves **45,083,592 distinct valid labeled boards** in **3,756,966 disjoint orbits** under color permutation and horizontal reflection, checked in [SplicePalCertificates.lean](SplicePalCertificates.lean). This adds **12,927,912 boards** to the [previous 32,155,680-board proof](SPLICE_RANGES.md).

| Source | Groups | Labeled boards |
|---|---:|---:|
| Previous certificate | 341 | 32,155,680 |
| New pivots sharing the earlier six caps | 12 | 3,477,672 |
| Families found by editing caps | 5 | 5,320,632 |
| Families found by rebuilding upper rows | 2 | 720,000 |
| Continuations of fifth-layer searches | 13 | 3,125,472 |
| Asymmetric caps at symmetric pivots | 5 | 31,560 |
| Caps and pivots symmetric in every row | 11 | 252,576 |
| **Total** | **389** | **45,083,592** |

The board has ten centered rows of lengths 1, 3, ..., 19. Each T reads one top cell and the three cells directly beneath it from left to right, and a valid board uses all 81 ordered color quadruples once. Fixing the eleven-cell sixth row (the pivot) splits the rest into a five-row cap and a four-row tail. Within each group, every cap pairs with the pivot to cover the same 25 patterns, and every tail pairs with the pivot to cover the other 56, so every listed cap fits every listed tail ([Splice.lean](Splice.lean)).

## Counting boards with mirror-symmetric upper rows

In all earlier families, the first six rows uniquely identify both the color permutation and the horizontal orientation. That requires at least one of the first six rows to differ from its reversal; otherwise the same prefix would match both orientations. The new supplement uses caps and pivots where **all six upper rows are palindromes**. Recoloring and reflection preserve row-by-row symmetry, so these boards cannot overlap any of the six earlier layers ([SplicePal.lean](SplicePal.lean)).

In these palindromic groups, reflecting a board leaves its cap and pivot fixed. We include both each tail and its row-by-row reflection in the sorted tail list, so reflected boards are already listed. Because the colors in each upper prefix first appear in the order 0, 1, 2, reading the order of first appearances after recoloring recovers the color permutation. Each cap-tail pair therefore gives 6 distinct labeled boards. The checker verifies that every tail has a distinct reflected partner in its group. Together these families add **252,576 boards** ([splice_pal.json](splice_pal.json)).

For example, the upper pattern set at pivot `20110201102` for discovery prefix `011100100001110002112112020110201102` admits four caps: two are row-by-row palindromes, and the other two are mirror images of each other. Exhausting this prefix found 1,938 tails, closed under reflection. The two symmetric caps in [splice_pal.json](splice_pal.json) yield 2 × 1,938 × 6 = **23,256** boards, while keeping one asymmetric cap in [splice_sixth.json](splice_sixth.json) and applying all twelve symmetries adds another **23,256**, for **46,512 boards** from this single pivot and upper pattern set.

## How many symmetric caps can share a pivot and pattern set?

An independent exhaustive search tested all 729 palindromic eleven-cell pivots using [find_palindromic_caps.py](find_palindromic_caps.py) (output in [splice-pal-census.log](splice-pal-census.log)). Starting at each pivot, it filled the cap upwards in mirrored pairs, pruning any repeated pattern right away, and kept canonical cap-pivot prefixes whose colors first appear in the order 0, 1, 2. Every valid six-row prefix must use all three colors, since two colors allow only 16 quadruples for 25 placements. The search found **3,548,213** canonical prefixes. Grouping them by pivot and 25-pattern set gives:

| Canonical symmetric caps in a group | Groups |
|---:|---:|
| 1 | 3,500,735 |
| 2 | 23,731 |
| 4 | 4 |

All four maximum-size groups extend to full valid boards, and all four appear in the certificate:

| Pivot | Canonical symmetric caps | Tails | Labeled boards |
|---|---:|---:|---:|
| `00120002100` | 4 | 4 | 96 |
| `00120102100` | 4 | 20 | 480 |
| `00122022100` | 4 | 4 | 96 |
| `10022122001` | 4 | 24 | 576 |

## Seven compatible caps from six

An earlier construction used six caps sharing the same 16 internal patterns. Changing a leftmost cell of color 2 to color 1 in each cap replaces the patterns `0210` and `2010` with `0110` and `1010`, so all six modified caps still share one internal pattern set. Searching upwards from pivot `22220210022` turns up a seventh compatible cap. All seven caps have one of only two bottom rows, `100000221` or `010000221`, differing only at the first two cells above the pivot triple `222`, so their nine crossing patterns match. With 15,539 recorded tails, this group gives **1,305,276 labeled boards**. A closely related seven-cap group at pivot `22221210022` exhausted its search at 19,707 tails, adding **1,655,388 boards** (recorded in [splice_sixth.json](splice_sixth.json) and replayable with [reproduce_splice.py](reproduce_splice.py)).

We found two five-cap groups by starting from a valid board, keeping row 6 and the 36 patterns above and crossing it, and searching upwards. At each step, the three colors below a cell narrow down which remaining patterns can supply its top color; any complete replacement uses the same 36 patterns, so the bottom three rows still fit. Two replacements gave distinct 25-pattern sets at the same pivot `00101101100`, and searching downwards from each prefix produced the recorded tails in [splice_sixth.json](splice_sixth.json).

Each continued group names the earlier cap family it extends. When a pivot and upper pattern set repeat, [SpliceRanges.lean](SpliceRanges.lean) checks that the new sorted tail interval starts strictly above the previous one; all other ordinary groups in [SpliceSixthCertificates.lean](SpliceSixthCertificates.lean) have distinct `(pivot, upper pattern set)` pairs.

## Verification

Lean checked the combined lower bound using only `propext`, `Classical.choice`, and `Quot.sound` (see [splice-pal-build.log](splice-pal-build.log)). An [independent audit](splice-pal-audit.log) ran the C++23 [Cartesian checker](expand_splice.cpp) to build all 45,083,592 labeled boards, check all 81 Cartesian T placements on each one, compare exact three-word base-three encodings for duplicates, and verify that the original 17,160-board family is included (you can also run the pure-Python expansion with `--expand`). Because the witnesses come from a mix of bounded and exhaustive searches, this is a lower bound; the unrestricted exact count is still open.

```sh
python prepare_splice_pal.py --build
python verify_splice.py --all --native --jobs 4
```

These commands repeat the palindromic census, reproduce the four-cap example with 24 tails, and replay a continuation to exhaustion (group numbers start at 1):

```sh
python find_palindromic_caps.py --census
python reproduce_splice.py --certificate splice_pal.json --exhaust 4
python reproduce_splice.py --certificate splice_sixth.json --exhaust 2
```
