# At least 348,960 three-color T boards

**Theorem.** There are at least **348,960** valid labeled boards with ten centered rows of lengths 1, 3, ..., 19. The certificate contains **29,080 distinct families** under global color permutation and horizontal reflection. It includes all 17,160 boards from the earlier certificate and adds 331,800 more.

## Cutting the board at row 5

Number the rows from 0 to 9 and read them left to right. A T between rows `r-1` and `r` has top color `rows[r-1][j]` and bottom colors `rows[r][j:j+3]`, giving `2r-1` placements in row `r`. A board is valid when those ordered color quadruples cover all 81 possibilities once each.

Fix the 11 colors in row 5. Call this row the **pivot**, the five rows above it a **cap**, and the four rows below it a **tail**. The T placements split cleanly at the pivot:

| Lower row of the T | Number of placements | Rows determining their colors |
|---|---:|---|
| 1 through 5 | 1 + 3 + 5 + 7 + 9 = 25 | Cap and pivot |
| 6 through 9 | 11 + 13 + 15 + 17 = 56 | Pivot and tail |

In each certificate group, every cap pairs with the pivot to cover the same 25 distinct patterns, and every tail pairs with that pivot to cover the remaining 56. Joining **any** cap in the group to **any** tail therefore uses all 81 patterns once. You can read off both choices directly from rows 0-4 and 6-9, so a group with $C$ caps and $T$ tails produces $C \times T$ distinct boards.

For example, group 13 uses pivot `22111212222`. Its four caps, written as rows of lengths 1, 3, 5, 7, and 9, are:

```text
1  000  01001  2102001  010001221
1  000  21001  0102001  010001221
1  001  01000  2102001  010001221
1  001  21000  0102001  010001221
```

Each of its 2,500 recorded tails fits all four caps, so this single group gives 10,000 representatives.

## Counting without overlap

From any complete board, you can read off both its pivot and the set of 25 patterns above the pivot. All 13 groups have different `(pivot, upper pattern set)` pairs, so their counts add without overlap.

| Group in the certificate | Caps | Tails | Representatives |
|---:|---:|---:|---:|
| 1 | 1 | 138 | 138 |
| 2 | 1 | 2,551 | 2,551 |
| 3 | 1 | 36 | 36 |
| 4 | 1 | 1,538 | 1,538 |
| 5 | 1 | 1,323 | 1,323 |
| 6 | 2 | 452 | 904 |
| 7 | 4 | 165 | 660 |
| 8 | 6 | 435 | 2,610 |
| 9 | 8 | 80 | 640 |
| 10 | 4 | 176 | 704 |
| 11 | 7 | 791 | 5,537 |
| 12 | 9 | 271 | 2,439 |
| 13 | 4 | 2,500 | 10,000 |
| **Total** | **49** | **10,456** | **29,080** |

Each of the six color permutations permutes the 81 ordered patterns bijectively. Reflecting every row swaps the left and right colors of each T and permutes the placements bijectively. All twelve operations preserve validity and can be inverted.

To separate the twelve operations, attach the board's apex color to both ends of its pivot row. Recoloring the board recolors this 13-digit string, and reflecting the board reverses it. For each of the twelve operations, collect the strings it produces across all recorded cap-pivot pairs. A finite check shows these twelve sets are pairwise disjoint. Any image therefore reveals which operation produced it, and undoing that operation recovers the original representative.

That gives **12 × 29,080 = 348,960** distinct labeled boards. The unrestricted exact count is still open.

## Checking the certificate

The [certificate file](splice_witnesses.json) stores every cap, pivot, and tail as base-3 digits. The [Python checker](verify_splice.py) enumerates geometric T placements in Cartesian coordinates, checks both pattern sets for each group, and verifies distinctness within groups, across groups, and across symmetry images. In expanded mode, it also builds every labeled board, checks all 81 placements on each, counts distinct full board strings, and verifies that the earlier 17,160-board family is included.

```sh
python verify_splice.py --expand
lake build SpliceCertificates
```

Lean proves `TBoards.at_least_348960` in [SpliceCertificates.lean](SpliceCertificates.lean) (using [Splice.lean](Splice.lean) and [SpliceSymmetry.lean](SpliceSymmetry.lean)), constructing an injection from `Fin 348960` into boards satisfying `TBoards.Valid`. Lean's kernel checks row lengths, colors, pattern coverage, and distinctness, multiplying the cap and tail list lengths directly. You can regenerate the Lean files with `python prepare_splice.py`.

## Reproducing the search

Each group stores one six-row discovery prefix. The forward search fills rows 6-9 in lexicographic order and rejects repeated patterns. It also tracks the ordered pair of colors at each end of each lower row: a triple `(l,m,r)` acts as a directed edge from `(l,m)` to `(m,r)`. Over all 81 patterns, every vertex has equal in-degree and out-degree. Inside a row, middle transitions cancel out, so the search can prune endpoint imbalances that the remaining rows cannot fix.

The reverse search fixes the pivot and the 25 upper patterns. Each triple in the pivot tells us which top colors are still unused, and repeating this step row by row reconstructs all compatible caps. The replay checks the full cap list and the requested number of forward-search tails against the saved lists (group 13 stops at 2,500 tails). The lower bound itself only needs the saved witnesses.

```sh
python reproduce_splice.py 3
python reproduce_splice.py --jobs 4
```

Groups 1-3 use the three six-row prefixes from Qiyuan Ma's five published representatives, and groups 4-5 change the apex of the second prefix. The rest use prefixes picked for having multiple interchangeable caps, including a mutation of the second prefix in group 13. The published certificate data are CC-BY-4.0; see [the source notices](sources/README.txt) and [Ma's certificate](https://doi.org/10.5281/zenodo.23631079).
