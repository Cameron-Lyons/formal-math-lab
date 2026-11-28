# At least 45,083,592 three-color T boards

This certificate pushes the proven lower bound past **45 million** valid labeled boards by combining four advances: opening an entirely new symmetry class where **every one of the first six rows is a palindrome**, conducting an exhaustive census of all palindromic 6-row prefixes, editing the earlier six-cap construction into **seven-cap** families, and continuing fifth-layer searches to exhaustion.

**Theorem.** There are at least **45,083,592 distinct valid labeled boards**, forming **3,756,966 disjoint orbits** of size 12 under global color permutation and horizontal reflection, verified in [SplicePalCertificates.lean](SplicePalCertificates.lean). This adds **12,927,912 boards** to the [previous 32,155,680-board proof](SPLICE_RANGES.md).

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

As in earlier layers, the board has ten centered rows of lengths $1, 3, \ldots, 19$; each upright T reads one top cell and the three cells directly beneath it left to right, and a valid board uses all $3^4 = 81$ ordered quadruples once. Fixing the 11-cell sixth row (the **pivot**) splits the board into a 5-row **cap** (25 patterns with the pivot) and a 4-row **tail** (56 patterns with the pivot), so within each group every listed cap fits every listed tail ([Splice.lean](Splice.lean)).

## Counting boards with mirror-symmetric upper rows

In all six earlier layers, Lean identified both the color permutation and the horizontal orientation of any transformed board by looking solely at its first six rows. That strategy *requires* at least one of the first six rows to differ from its reversal — otherwise horizontal reflection leaves the entire 6-row prefix unchanged!

The new supplement targets exactly the excluded case: caps and pivots where **all six upper rows are palindromes**. Because global recoloring and horizontal reflection both preserve row-by-row palindromicity, no board in this family can ever collide with any board from the six earlier layers ([SplicePal.lean](SplicePal.lean)).

How do we count symmetry images cleanly when horizontal reflection fixes the cap and pivot?

1. **Absorb reflection into the tail list.** Reflecting a board with a palindromic cap and pivot leaves rows 0–5 unchanged and reflects rows 6–9 (the tail). Instead of applying reflection externally, we store *both* each tail and its row-by-row reflection inside the sorted tail list. The checker verifies that every tail has a distinct reflected partner in its group (no valid board can be horizontally symmetric as a whole).
2. **Apply only the 6 color permutations externally.** Every stored palindromic prefix uses all three colors in canonical first-appearance order `0, 1, 2`. After applying any color permutation, simply reading the order in which the three distinct colors first appear in rows 0–5 uniquely recovers which of the 6 permutations was applied!

Each `(cap, tail)` pair in a palindromic group therefore contributes **6** distinct labeled boards (with horizontal reflection already accounted for by the paired tails). Together, these 11 palindromic families add **252,576 boards** ([splice_pal.json](splice_pal.json)).

**Worked example.** Consider the pivot `20110201102` and its 36-cell palindromic discovery prefix `011100100001110002112112020110201102` (rows `0`, `111`, `00100`, `0011100`, `021121120`, `20110201102`). Its 25-pattern set admits **four** compatible caps: two are row-by-row palindromes, and the other two are asymmetric mirror images of each other. Exhausting this prefix finds **1,938 tails**, closed under reflection:

* The **2 symmetric caps** (stored in [splice_pal.json](splice_pal.json)) yield $2 \times 1{,}938 \times 6 = \mathbf{23{,}256}$ labeled boards.
* Keeping **1 asymmetric cap** from the mirror pair (stored in [splice_sixth.json](splice_sixth.json)) and applying all 12 symmetries adds another $1 \times 1{,}938 \times 12 = \mathbf{23{,}256}$ labeled boards.

In total, this single `(pivot, upper pattern set)` yields **46,512 distinct labeled boards**.

## How many symmetric caps can share a pivot and pattern set?

How large can a fully palindromic cap family possibly get? Since an 11-cell palindrome is determined by its first six cells, there are only $3^6 = 729$ palindromic pivots. An independent exhaustive search tested all **729** palindromic pivots using [find_palindromic_caps.py](find_palindromic_caps.py) (complete output in [splice-pal-census.log](splice-pal-census.log)).

Starting from each pivot, the search filled the cap upward in mirrored cell pairs, pruned repeated patterns immediately, and retained canonical prefixes whose colors first appear in the order `0, 1, 2`. (Every valid 6-row prefix *must* use all three colors, because two colors can supply at most $2^4 = 16$ quadruples for 25 placements.) The census found exactly **3,548,213** canonical palindromic prefixes. Grouping them by `(pivot, 25-pattern set)` proves that **4 is the exact maximum**:

| Canonical symmetric caps in a group | Groups |
|---:|---:|
| 1 | 3,500,735 |
| 2 | 23,731 |
| 4 | 4 |

Remarkably, all four maximum-size groups extend to full 100-cell valid boards, and all four appear in the certificate:

| Pivot | Canonical symmetric caps | Tails | Labeled boards |
|---|---:|---:|---:|
| `00120002100` | 4 | 4 | 96 |
| `00120102100` | 4 | 20 | 480 |
| `00122022100` | 4 | 4 | 96 |
| `10022122001` | 4 | 24 | 576 |

## Seven compatible caps from six

The biggest numerical gains in this layer come from three further ordinary-prefix constructions recorded in [splice_sixth.json](splice_sixth.json):

* **Editing six caps into seven:** Start from the earlier six-cap family (sharing 16 internal patterns). Changing a leftmost cell of color `2` to color `1` in every cap replaces the internal patterns `0210` and `2010` with `0110` and `1010`, so all six edited caps still share one internal pattern set. Searching upward from pivot `22220210022` reveals a **seventh** compatible cap! All seven caps end in either `100000221` or `010000221`, differing only at the first two cells above the pivot's repeated `222` triples, so all nine crossing patterns match. With 15,539 recorded tails, this group delivers $7 \times 15{,}539 \times 12 = \mathbf{1{,}305{,}276}$ labeled boards. A closely related seven-cap group at pivot `22221210022` exhausted its search at 19,707 tails, adding $7 \times 19{,}707 \times 12 = \mathbf{1{,}655{,}388}$ boards (replayable with [reproduce_splice.py](reproduce_splice.py)).
* **Rebuilding upper rows above row 6:** We found two five-cap groups by taking a valid board, fixing **row 6** along with the 36 patterns above and crossing row 6, and searching upward. At each step, the three colors below a cell narrow down which remaining patterns can supply its top color; any complete replacement uses the exact same 36 patterns, guaranteeing the original bottom three rows still fit. Two replacements yielded distinct 25-pattern sets at the same pivot `00101101100`, and forward searches from each prefix produced the recorded tails in [splice_sixth.json](splice_sixth.json).
* **Continuations and range disjointness:** Each continued group names the earlier cap family it extends. Whenever a `(pivot, upper pattern set)` repeats across layers, [SpliceRanges.lean](SpliceRanges.lean) checks that the new sorted tail interval starts strictly above the previous maximum tail code; all other ordinary groups in [SpliceSixthCertificates.lean](SpliceSixthCertificates.lean) have pairwise distinct `(pivot, upper pattern set)` pairs.

## Verification

Lean verified the combined 45,083,592-board lower bound using only its standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` (see [splice-pal-build.log](splice-pal-build.log)). An [independent audit](splice-pal-audit.log) ran the C++23 [Cartesian checker](expand_splice.cpp) to materialize all 45,083,592 labeled boards, check all 81 Cartesian T placements on every board, compare exact three-word base-3 encodings to rule out duplicates, and verify that the original 17,160-board family is included (you can also run the pure-Python expansion with `--expand`). Because the witnesses come from a mix of bounded and exhaustive searches, this establishes a lower bound; the unrestricted exact count remains open.

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
