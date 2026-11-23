# At least 348,960 three-color T boards

**Theorem.** There are at least **348,960** valid labeled boards with ten centered rows of lengths 1, 3, …, 19. The certificate contains **29,080 distinct families** under global color permutation and horizontal reflection. It includes all 17,160 boards in the earlier certificate, adding 331,800.

## Cutting the board at row 5

Index the rows from 0 to 9 and read them left to right. A T between rows `r−1` and `r` has upper color `rows[r−1][j]` and lower colors `rows[r][j:j+3]`. There are `2r−1` such placements. Validity means their ordered color quadruples cover all 81 possibilities exactly once.

Fix the eleven colors in row 5. Call this row the **pivot**, the five rows above it a **cap**, and the four rows below it a **tail**. The T placements split at the pivot:

| Lower row of the T | Number of placements | Rows determining their colors |
|---|---:|---|
| 1 through 5 | 1 + 3 + 5 + 7 + 9 = 25 | Cap and pivot |
| 6 through 9 | 11 + 13 + 15 + 17 = 56 | Pivot and tail |

In each certificate group, every cap with the pivot realizes the same 25 distinct patterns. Every tail with that pivot realizes the remaining 56. Joining **any** cap in the group to **any** tail therefore uses every pattern exactly once. The two choices can be recovered by reading rows 0–4 and 6–9, so a group with $C$ caps and $T$ tails gives $C \times T$ distinct boards.

For example, group 13 uses pivot `22111212222`. Its four caps, written as consecutive rows of lengths 1, 3, 5, 7 and 9, are

```text
1  000  01001  2102001  010001221
1  000  21001  0102001  010001221
1  001  01000  2102001  010001221
1  001  21000  0102001  010001221
```

Each of its 2,500 recorded tails fits all four caps. This one group supplies 10,000 representatives.

## Counting without overlap

The pivot and the set of patterns above it can both be read from a complete board. The 13 groups have distinct pairs of these values. Their products therefore add.

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

Each of the six color permutations bijects the ordered patterns. Reflecting every row exchanges the left and right colors of each T and bijects the placements. All twelve operations preserve validity and each is invertible.

To distinguish the operations, read a short string from a board by placing its apex color at both ends of its pivot row. Recoloring a board recolors this string, and reflecting the board reverses it. For each of the twelve operations, take the set of strings it produces from all recorded cap–pivot pairs. The finite check verifies that these twelve sets are pairwise disjoint. Thus an image determines which operation produced it. Inverting that operation then determines the original representative.

This gives **12 × 29,080 = 348,960** distinct labeled boards. The unrestricted total remains open in this computation.

## Checking the certificate

The data file contains every cap, pivot and tail as ternary digits. The Python checker enumerates the geometric T placements in Cartesian coordinates, checks both pattern sets for each group, and verifies distinctness within and between groups and symmetry images. Its expanded mode also assembles every labeled board, checks all 81 placements on each, counts the distinct full board strings, and checks inclusion of the earlier family. [Certificate](splice_witnesses.json) · [Python checker](verify_splice.py)

```sh
python verify_splice.py --expand
lake build SpliceCertificates
```

Lean proves `TBoards.at_least_348960`, an injection from `Fin 348960` into boards satisfying the original `TBoards.Valid` predicate. Its kernel checks row lengths, colors, pattern coverage and distinctness. The proof uses the cap and tail lists independently and multiplies their lengths. The certificate generator can be rerun with `python prepare_splice.py`. [Final theorem](SpliceCertificates.lean) · [Splice proof](Splice.lean) · [Symmetry proof](SpliceSymmetry.lean)

## Reproducing the search

Each group records one six-row discovery prefix. The forward search fills rows 6–9 in lexicographic order, rejecting repeated patterns. It also tracks the ordered pair at each end of each lower row. A triple `(l,m,r)` contributes a directed edge from `(l,m)` to `(m,r)`. All 81 patterns together give each vertex equal incoming and outgoing degree. Within a row the interior contributions cancel, which allows the search to discard endpoint imbalances that the remaining rows cannot repair.

The reverse search fixes the pivot and the 25 upper patterns. Reading triples in the pivot determines which upper colors are available. Repeating this one row at a time reconstructs the compatible caps. The replay compares the complete cap list and the requested number of forward-search tails with the saved lists. Group 13 stops at 2,500 tails. The lower bound needs only the recorded witnesses.

```sh
python reproduce_splice.py 3
python reproduce_splice.py --jobs 4
```

Groups 1–3 use the three different six-row prefixes in Qiyuan Ma’s five published representatives. Groups 4–5 change the apex of the second prefix. The remaining groups use prefixes selected for interchangeable caps, including a mutation of the second prefix in group 13. The published certificate data are CC-BY-4.0. [Source notices](sources/README.txt) · [Ma’s certificate](https://doi.org/10.5281/zenodo.23631079)
