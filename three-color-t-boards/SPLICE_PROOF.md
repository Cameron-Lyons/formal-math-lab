# At least 348,960 three-color T boards

Finding valid boards one by one scales linearly with search time. We can do much better by **splicing**: cutting the 10-row ziggurat horizontally through its middle row so that interchangeable top halves and compatible bottom halves combine multiplicatively.

**Theorem.** There are at least **348,960** valid labeled boards with ten centered rows of lengths $1, 3, \ldots, 19$. The certificate contains **29,080 distinct families** (orbits of size 12) under global color permutation and horizontal reflection. It includes all 17,160 boards from the earlier certificate and adds 331,800 more.

## Cutting the board at row 5

Number the rows from $0$ at the top to $9$ at the bottom, reading each row left to right. Every upright T-tetromino between rows $r - 1$ and $r$ reads its top cell `rows[r-1][j]` together with three consecutive bottom cells `rows[r][j:j+3]`, giving $2r - 1$ placements anchored on row $r$ ($1 + 3 + \cdots + 17 = 81$ in total). A board is valid when those 81 ordered quadruples cover all $3^4 = 81$ patterns once each.

Now fix the 11 colors of **row 5**. Call row 5 the **pivot**, the five rows above it (rows 0–4) a **cap**, and the four rows below it (rows 6–9) a **tail**:

```text
  rows 0–4  (lengths 1, 3, 5, 7, 9)   ← cap    ┐ 25 upper T placements
  row 5     (length 11)               ← pivot  ┼
  rows 6–9  (lengths 13, 15, 17, 19)  ← tail   ┘ 56 lower T placements
```

Because every T spans only two adjacent rows, no T ever touches both the cap and the tail! The 81 placements split cleanly at the pivot:

| Lower row of the T | Number of placements | Rows determining their colors |
|---|---:|---|
| 1 through 5 | $1 + 3 + 5 + 7 + 9 = 25$ | Cap and pivot |
| 6 through 9 | $11 + 13 + 15 + 17 = 56$ | Pivot and tail |

This clean separation is the entire engine of the proof. In each certificate **group**, we fix a pivot and a set of 25 upper patterns:

* Every listed **cap** combines with the pivot to produce that exact set of 25 distinct patterns.
* Every listed **tail** combines with the pivot to produce the exact complementary set of 56 patterns.

Gluing **any** cap in the group to **any** tail in the group therefore covers all $25 + 56 = 81$ patterns without overlap. Because you can read off both the cap (rows 0–4) and the tail (rows 6–9) directly from the finished board, a group with $C$ caps and $T$ tails generates $C \times T$ distinct valid boards.

**Worked example (Group 13).** Group 13 fixes the pivot `22111212222`. Its four caps, written as rows of lengths 1, 3, 5, 7, and 9, are:

```text
1  000  01001  2102001  010001221
1  000  21001  0102001  010001221
1  001  01000  2102001  010001221
1  001  21000  0102001  010001221
```

Notice that all four caps share the exact same row 4 (`010001221`), so their nine crossing Ts into the pivot are identical automatically, while rows 0–3 rearrange the 16 internal patterns into the same set. Each of group 13's 2,500 recorded tails fits all four caps, yielding $4 \times 2{,}500 = 10{,}000$ representatives (120,000 labeled boards) from a single group.

## Counting without overlap

To sum across all 13 groups safely, we check two kinds of disjointness: between groups, and across the 12 symmetries.

**Disjointness across groups.** From any complete board, you can read off both its pivot (row 5) and the set of 25 patterns formed in rows 0–5. All 13 groups have distinct `(pivot, upper pattern set)` pairs, so boards from different groups can never coincide. Their representative counts therefore add directly:

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

**Disjointness across all 12 symmetry images.** Each of the 6 color permutations permutes the 81 ordered patterns bijectively, and horizontal reflection reverses every row — swapping the left and right colors of each T and permuting placements bijectively. All 12 symmetry operations preserve validity and are invertible.

How do we verify quickly that applying all 12 operations to all 29,080 representatives produces no collisions? From any board, extract a compact 13-digit signature by attaching its apex color (row 0) to both ends of its pivot row:

$$
\text{tag} = \text{apex} + \text{pivot} + \text{apex}.
$$

Recoloring the board recolors this 13-digit string, and reflecting the board reverses it. For each of the 12 symmetry operations, collect all 13-digit tags it produces across the 49 recorded cap–pivot pairs. A finite check confirms that these 12 sets of tags are **pairwise disjoint**. Given any resulting labeled board, its tag immediately tells you *which* of the 12 operations produced it; applying the inverse operation recovers the unique original representative (and hence its group, cap, and tail).

Multiplying gives **$12 \times 29{,}080 = 348{,}960$** distinct labeled boards. The unrestricted exact count remains open.

## Checking the certificate

The [certificate file](splice_witnesses.json) stores every cap, pivot, and tail as base-3 digits. The [Python checker](verify_splice.py) enumerates geometric T placements in Cartesian coordinates, checks both pattern sets for each group, and verifies distinctness within groups, across groups, and across symmetry images. In expanded mode, it builds all 348,960 labeled boards, checks all 81 placements on each, counts distinct full board strings, and verifies that the earlier 17,160-board family is contained inside it.

```sh
python verify_splice.py --expand
lake build SpliceCertificates
```

Lean proves `TBoards.at_least_348960` in [SpliceCertificates.lean](SpliceCertificates.lean) (using [Splice.lean](Splice.lean) and [SpliceSymmetry.lean](SpliceSymmetry.lean)), explicitly constructing an injection from `Fin 348960` into boards satisfying `TBoards.Valid`. Lean's kernel verifies row lengths, colors, pattern coverage, and distinctness, multiplying the cap and tail list lengths directly. You can regenerate the Lean files with `python prepare_splice.py`.

## Reproducing the search

Each group stores a single six-row discovery prefix. Two complementary searches populate the witness lists:

* **Forward tail search (rows 6–9):** fills the bottom four rows in lexicographic order, rejecting repeated patterns immediately. It also exploits a **de Bruijn graph balance constraint**: view each three-cell bottom bar $(l, m, r)$ as a directed edge from the color pair $(l, m)$ to $(m, r)$. Across all 81 patterns, every pair vertex has equal in-degree and out-degree. Inside any single row, consecutive edges share interior pairs that cancel out, leaving only the leftmost and rightmost pairs of the row. The solver tracks these endpoint imbalances and prunes any branch whose remaining rows cannot possibly restore balance.
* **Reverse cap search (rows 4 down to 0):** fixes the pivot and the 25 upper patterns. Each three-cell slice of the pivot restricts which unused upper patterns can supply its top cell in row 4; iterating upward row by row reconstructs every cap compatible with that `(pivot, upper pattern set)` pair.

The replay script verifies the complete cap list and the requested number of forward-search tails against the saved witness file (group 13 stops at 2,500 tails). The lower bound itself depends only on the saved witnesses, not on the search code.

```sh
python reproduce_splice.py 3
python reproduce_splice.py --jobs 4
```

Groups 1–3 use the three six-row prefixes from Qiyuan Ma's five published representatives, and groups 4–5 change the apex of the second prefix. The remaining groups use prefixes chosen for having multiple interchangeable caps, including a mutation of the second prefix in group 13. The published certificate data are CC-BY-4.0; see [the source notices](sources/README.txt) and [Ma's certificate](https://doi.org/10.5281/zenodo.23631079).
