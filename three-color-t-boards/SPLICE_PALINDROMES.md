# At least 45,083,592 three-color T boards

The certificate gives **45,083,592 distinct valid labeled boards** in **3,756,966 disjoint orbits** under color permutation and horizontal reflection. The gain over the previous lower bound of 32,155,680 is **12,927,912 boards**. [Combined Lean theorem](SplicePalCertificates.lean) · [Previous proof](SPLICE_RANGES.md)

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

The board has ten centered rows of lengths 1, 3, …, 19. A T reads a top cell and the three cells immediately below it from left to right. Validity requires all 81 possible color quadruples to occur once. Fixing the eleven-cell sixth row, called the pivot, separates the remaining cells into a five-row cap and a four-row tail. In each group, every cap with the pivot realizes the same 25 patterns, and every tail with the pivot realizes the complementary 56. Every listed cap therefore fits every listed tail. [Splice proof](Splice.lean)

## Counting boards with mirror-symmetric upper rows

In the earlier families, the first six rows identify the color permutation and orientation used to produce a board. Consequently at least one of those rows differs from its reversal. Otherwise the same prefix would identify two orientations. The new supplement uses caps and pivots in which **every one of the first six rows is a palindrome**. That property survives both reflection and recoloring, so it separates the supplement from all six ordinary layers. [Disjointness proof](SplicePal.lean)

In these groups, reflecting a board fixes its cap and pivot. We include both a tail and its row-by-row reflection in the sorted tail list. Their reflected images are already represented. The colors of each upper prefix first appear in the order 0, 1, 2, so the first appearances after recoloring identify the palette. Hence each cap–tail pair contributes exactly six distinct labeled boards. The checker confirms that every tail has a distinct partner in its group. Together these families account for **252,576 boards**. [Palindromic witnesses](splice_pal.json)

For example, the upper pattern set at pivot `20110201102` for discovery prefix `011100100001110002112112020110201102` admits four caps. Two are palindromes row by row. The other two are reflections of each other. The search exhausted the prefix at 1,938 tails, a set closed under reflection. The two symmetric caps give 2 × 1,938 × 6 = **23,256** boards. Keeping one of the asymmetric caps and applying all twelve operations gives another **23,256**. Their common upper pattern set and pivot thus yield **46,512 boards**. [Ordinary witnesses](splice_sixth.json) · [Symmetric witnesses](splice_pal.json)

## How many symmetric caps can share a pivot and pattern set?

An independent exhaustive search considered all 729 palindromic eleven-cell pivots. Starting at each pivot, it filled the cap upwards in mirrored pairs, rejecting repeated upper patterns immediately. It retained cap–pivot prefixes whose colors first appear as 0, 1, 2. Every admissible six-row prefix uses all three colors, since two colors provide only 16 possible quadruples for 25 placements. The enumeration found **3,548,213** canonical prefixes. Grouping by the exact pivot and the 25-pattern set gives these counts. [Enumeration program](find_palindromic_caps.py) · [Census output](splice-pal-census.log)

| Canonical symmetric caps in a group | Groups |
|---:|---:|
| 1 | 3,500,735 |
| 2 | 23,731 |
| 4 | 4 |

All four groups attaining the maximum have full-board completions. Each appears in the certificate.

| Pivot | Canonical symmetric caps | Tails | Labeled boards |
|---|---:|---:|---:|
| `00120002100` | 4 | 4 | 96 |
| `00120102100` | 4 | 20 | 480 |
| `00122022100` | 4 | 4 | 96 |
| `10022122001` | 4 | 24 | 576 |

## Seven compatible caps from six

A previous construction used six caps with the same 16 internal patterns. In each cap, changing a leftmost cell of color 2 to color 1 replaces the patterns `0210` and `2010` by `0110` and `1010`. Thus six modified caps again share an internal pattern set. Enumerating upwards from pivot `22220210022` gives a seventh compatible cap. The seven have only two different bottom rows, `100000221` and `010000221`. They differ at the first two cells, both above the same pivot triple `222`. The nine crossing patterns consequently agree for all seven caps. With 15,539 recorded tails, this group gives **1,305,276 labeled boards**. A related seven-cap group at pivot `22221210022` exhausted its search at 19,707 tails, giving a further **1,655,388 boards**. [Upper sections and replay](reproduce_splice.py) · [New ordinary groups](splice_sixth.json)

We found two five-cap groups by starting from a verified board, keeping its seventh row and the 36 patterns above and across it, and enumerating upwards. At each step, the three colors below a proposed cell determine which of the remaining patterns can supply its top color. A complete replacement uses exactly the original 36 patterns, so the original bottom three rows still fit. Two replacements yielded different 25-pattern sets at the same pivot, `00101101100`. Searching downwards from each new prefix then supplied its full list of recorded tails. [New ordinary groups](splice_sixth.json)

The continued groups name the earlier cap family they extend. For a repeated pivot and upper pattern set, Lean checks that each new sorted interval of tails starts strictly after the preceding interval. The other ordinary groups are separated by their pivot and upper pattern set. [Interval proof](SpliceRanges.lean) · [Six-layer theorem](SpliceSixthCertificates.lean)

## Verification

Lean checked the combined lower bound using `propext`, `Classical.choice`, and `Quot.sound`. The independent audit constructed all 45,083,592 labeled boards, evaluated the 81 Cartesian T placements on each, and compared complete base-three encodings for duplicates. It also confirmed inclusion of the original 17,160-board family. The C++23 checker uses three exact base-three integers for each 100-cell board. The Python-only checker can repeat the expansion with `--expand`. The lower bound counts the recorded pieces from bounded or exhaustive searches. The unrestricted exact count remains open. [Lean build](splice-pal-build.log) · [Cartesian checker](expand_splice.cpp) · [Independent audit](splice-pal-audit.log)

```sh
python prepare_splice_pal.py --build
python verify_splice.py --all --native --jobs 4
```

The following commands repeat the census, reproduce the four-cap example with 24 tails, and replay a continuation to exhaustion. The group numbers in the replay commands start at one.

```sh
python find_palindromic_caps.py --census
python reproduce_splice.py --certificate splice_pal.json --exhaust 4
python reproduce_splice.py --certificate splice_sixth.json --exhaust 2
```
