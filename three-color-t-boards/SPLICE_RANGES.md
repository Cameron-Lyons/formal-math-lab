# At least 32,155,680 three-color T boards

Three new ideas push the certified lower bound past **32 million** boards: a clean 10-pivot family sharing six interchangeable caps, a new record of **15 interchangeable caps** built with a single occurrence of color `2`, and **lexicographic range continuations** that resume earlier truncated tail searches right where they stopped without overlapping a single board.

**Theorem.** There are at least **32,155,680 distinct valid labeled boards**, forming **2,679,640 disjoint orbits** of size 12 under global color permutation and horizontal reflection. This adds **10,996,944 boards** to the [previous lower bound](SPLICE_FURTHER.md) of 21,158,736, verified in [SpliceNextCertificates.lean](SpliceNextCertificates.lean).

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

Recall the splicing split ([Splice.lean](Splice.lean)): a valid board covers all 81 ordered color quadruples across its 81 T placements, and fixing the 11-cell sixth row (the **pivot**) separates the 25 placements in the 5-row **cap** plus pivot from the 56 placements in the pivot plus 4-row **tail**. Whenever those two pattern sets are complementary, every cap fits every tail.

The six caps used here all share the exact same 16 internal patterns, and every one of them ends in one of just two row-4 strings:

```text
010000221
100000221
```

Notice that these two bottom rows differ *only* by swapping their first two cells (`01...` vs. `10...`). Now pick any pivot that begins with **four identical digits** (such as `2222...`, or `1111...`). Its first two three-cell slices are identical (`222` and `222`), so swapping the first two cells above them merely trades the positions of the two crossing patterns `0222` and `1222` — leaving the *set* of all nine crossing patterns unchanged! As long as all nine crossing patterns are distinct and disjoint from the 16 internal patterns, all six caps produce the exact same 25 upper patterns.

The ten pivots below pass that check, with their explicit caps, pivots, and tails recorded in [splice_next.json](splice_next.json). Every one of the six caps fits every tail in its row, contributing **$6 \times 76{,}809 \times 12 = 5{,}530{,}248$ labeled boards**:

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

Earlier binary caps (using only colors `0` and `1`) peaked at 12 interchangeable caps per group. Moving one tiny step away from purely binary caps — allowing **exactly one occurrence of color `2`** across the 25 cells of the cap (thirteen `0`s, eleven `1`s, and a single `2`) — breaks that ceiling.

The pivot `20121212001` admits **15 different caps** producing the exact same 25 upper patterns:

* Thirteen of those caps share the same 16 internal patterns.
* The other two have slightly different internal pattern sets, yet their nine crossing placements into the pivot supply the exact missing patterns so the 25-pattern union stays identical!

With **1,419 recorded tails**, this single pivot produces **$15 \times 1{,}419 \times 12 = 255{,}420$ labeled boards**. A second pivot, `01021212102`, also admits 15 compatible caps; its 206 recorded tails add another **37,080** labeled boards.

To discover these groups, we enumerated five-row caps containing a single `2`, grouped them by their internal patterns, and checked which bottom rows produce matching crossing patterns for a fixed pivot. A reverse search using all 25 patterns then recovered the complete cap lists; all caps and tails are stored in [splice_next.json](splice_next.json) and verified in Lean.

You can reproduce both 15-cap families directly from their pivots using [find_rare_caps.py](find_rare_caps.py), which enumerates single-2 caps and groups them by all 25 upper patterns. At `20121212001`, 19,347 valid single-2 caps produce 17,349 distinct 25-pattern sets, and only one pattern set appears on 15 or more caps:

```sh
python find_rare_caps.py 20121212001
python find_rare_caps.py 01021212102
```

## Extending a search past its previous cutoff

Six older four-cap prefixes in [splice_further.json](splice_further.json) had previously been capped at 3,500 tails. Using [splice_search.cpp](splice_search.cpp), we resumed each search *immediately after* its last recorded tail in lexicographic order and exhausted all remaining tails for all six prefixes — uncovering **44,138 additional tails** for four caps each. The largest continuation alone adds 13,684 tails, or $12 \times 4 \times 13{,}684 = 656{,}832$ labeled boards.

How does Lean certify that a continuation group does not overlap the earlier group it extends, given that both share the exact same `(pivot, upper pattern set)`? Every full board determines its pivot, upper pattern set, and tail. Groups with different `(pivot, upper pattern set)` pairs cannot overlap. When a continuation repeats an earlier `(pivot, upper pattern set)`, [SpliceRanges.lean](SpliceRanges.lean) simply verifies that the **largest earlier tail code is strictly smaller than the smallest new tail code** — since all tails have the same length, base-3 integer order agrees with lexicographic order, guaranteeing the two tail ranges are completely disjoint! To keep all twelve symmetry images separate across the entire certificate, [SplicePrefixSymmetry.lean](SplicePrefixSymmetry.lean) reads the transformed six upper rows, identifies the symmetry operation, and inverts it.

Five additional new prefixes came from fixing the lower rows of an existing valid board and rebuilding its upper rows from the remaining 25 patterns. One of them, at pivot `00110011002`, admits 12 caps and 3,561 tails, contributing $12 \times 12 \times 3{,}561 = 512{,}784$ labeled boards. Each group counts only its explicit cap–tail products; the exact unrestricted total remains unknown.

## Reproducing the checks

Run these commands from the proof directory to regenerate the new Lean files, check the combined theorem, and independently expand every labeled board:

```sh
python prepare_splice_next.py
lake build SpliceNextCertificates
python verify_splice.py --through-next --expand --jobs 3
```

The [independent checker](verify_splice.py) builds every symmetry image, evaluates its 81 Cartesian T placements, checks for duplicate 100-digit boards using exact base-3 encodings, and confirms that the original 17,160-board family is included (see the [expanded audit](splice-next-audit.log)). The Lean theorem relies only on the standard axioms `propext`, `Classical.choice`, and `Quot.sound` (see the [Lean build log](splice-next-lean-build.log)).

The discovery replay accepts one-based group numbers (omitting them replays all new groups up to their recorded bounds). For example, this command exhausts continuation group 9 and reproduces its four caps and 5,411 new tails:

```sh
python reproduce_splice.py --certificate splice_next.json --exhaust 9
```
