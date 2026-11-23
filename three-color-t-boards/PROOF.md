# More than sixty three-color T boards

**Theorem.** There are at least **72 distinct labeled colorings** of the centered
board with row lengths $1,3,\ldots,19$, using colors $0,1,2$, in which each
of the $3^4=81$ ordered T patterns occurs exactly once. A T consists of one
cell directly above the middle of three consecutive cells. Only translates
of this orientation are counted; color names and reflected boards count
separately.

Use `0 = red`, `1 = green`, and `2 = blue`; read each pattern in the
order (top, left, middle, right).

This proves that there are more than 60 such boards. The proof consists of
six explicit boards, a finite validity table, and a symmetry argument.
Board A below is also explicitly outside all five published families,
as proved in the novelty argument below.

## Six boards

Number the rows from 0 at the top to 9 at the bottom, and read each row from
left to right. All six boards start with these seven rows:

```text
row   colors
 0    0
 1    000
 2    21121
 3    2102221
 4    010122001
 5    22111212222
 6    0120111221110
```

Append one of the following endings:

| Board | Row 7 | Row 8 | Row 9 |
|---|---|---|---|
| A | `001022002021212` | `10110022000210001` | `1202021011020120100` |
| B | `002011000212101` | `10202202100020012` | `1200101102120220100` |
| C | `100220200010002` | `21202020101102101` | `0210011022012002121` |
| D | `101011000012120` | `20200210220022010` | `1001100202021021201` |
| E | `201002000212101` | `10110202100020220` | `1001200102120220110` |
| F | `212021210220200` | `00021000100201101` | `1022012020010110021` |

Every row has the prescribed length, so these are six 100-cell boards.

## Every pattern occurs exactly once

Write $a_r(j)$ for entry $j$ of row $r$, indexing entries from 0.
The cell has coordinates $(j-r,-r)$. Consequently, every translated T
has exactly the form

$$
W_{r,j}=\bigl(a_{r-1}(j),a_r(j),a_r(j+1),a_r(j+2)\bigr),
\qquad 1\le r\le9,\quad 0\le j\le2r-2.
$$

Indeed, the lower middle cell has coordinates $(j+1-r,-r)$, and
the upper cell has the same horizontal coordinate. The three lower cells
fit precisely for the stated values of $j$, and their upper cell then
lies in row $r-1$. Conversely, any T has a lower row and a leftmost
lower cell, which determine $r,j$. Thus this lists all placements
without repetition. There are

$$
1+3+5+\cdots+17=81
$$

of them. Encode an ordered color pattern by

$$
E(t,l,m,u)=27t+9l+3m+u.
$$

Base-three notation makes $E$ a bijection between the 81 color patterns
and the integers $0,\ldots,80$. The complete code table below gives
$E(W_{r,j})$ from left to right for every row. For each board, its six
shared lines and its three individual lines contain every integer from
0 to 80 exactly once. Therefore all six boards have the required property.

For example, board A's first window in row 7 is $(0,0,0,1)$, with
code 1. Its first window in row 8 is $(0,1,0,1)$, with code 10.

## Why these give 72 different boards

Permuting the three color names preserves the property: it permutes the
81 ordered patterns bijectively. Reflecting every row also preserves it:
reflection bijects the T placements and sends the pattern
$(t,l,m,u)$ to $(t,u,m,l)$. Each listed board therefore has
$3!\cdot2=12$ valid symmetry images, initially allowing repetitions.

It remains to show that these 72 images are all different. Suppose two
images coincide. Undoing one of their transformations would take one of
the six listed boards to another by a color permutation, possibly followed
by reflection.

Reflection is impossible. All six boards have row 2 equal to `21121`.
In that row, entries 0 and 2 are different. In its reversal `12112`,
entries 0 and 2 are equal, and a color permutation preserves equality.
Thus no recolored reflection can have the required row 2.

Without reflection, the color permutation must fix 0 because of the top
cell. It must also fix 2 and 1 because of entries 0 and 1 of row 2.
It is therefore the identity. Finally, the six listed boards are distinct:
the first three entries of row 7 are respectively
`001`, `002`, `100`, `101`, `201`, and `212`.

Hence equality is possible only for the same board with the same
transformation. There are at least $6\cdot12=72>60$ valid boards. **QED.**

## Board A is outside all five published families

This also meets the question's specific request for a new board. The five
published representatives in [the supplied certificate](sources/anc/certificates.json)
all have apex color 0 and fall into these two groups (rows are still numbered
from 0):

| Published representatives | Row 2 | Row 6 |
|---|---|---|
| Three representatives | `00100` | Not needed |
| The other two representatives | `21121` | `0201201111202` |
| Board A | `21121` | `0120111221110` |

Suppose a published representative could be recolored, with or without
reflection, to give A. The apex forces the recoloring to fix color 0.
The three representatives in the first group have zeros in row 2, while A
has none. Thus they cannot give A, even after reflection.

For the other two representatives, a reflected row 2 would be `12112`.
Its entries 0 and 2 are equal, whereas those entries of A's `21121` differ.
No recoloring can repair this. Without reflection, matching row 2 forces
the recoloring to fix colors 1 and 2 as well, so it is the identity. But
row 6 then differs from A's. This excludes the other two representatives.

Therefore A is unequal to **every one of the 60 published boards**. Since
the code table proves A valid, A alone, together with the published 60,
already answers the question affirmatively. The six-board proof above
establishes the stronger bound of 72 without relying on the published count.

## Complete finite check

The numbers below are decimal codes; leading zeros are just for alignment.
The first block is used for each of A through F.

```text
Shared rows:
  1: 00
  2: 22 14 16
  3: 75 38 35 80 52
  4: 57 37 05 71 78 72 28
  5: 25 49 13 41 70 77 17 26 53
  6: 59 69 46 31 40 68 44 79 76 67 66
A:
  7: 01 30 65 08 51 45 29 60 74 34 50 43 23
  8: 10 04 39 09 56 62 24 18 54 02 61 48 63 27 55
  9: 42 20 33 47 07 21 64 58 12 11 06 73 32 15 19 03 36
B:
  7: 02 33 73 04 39 36 27 56 61 50 43 48 10
  8: 11 06 74 08 51 47 07 21 09 54 29 60 45 01 32
  9: 42 18 55 03 64 58 12 65 34 23 15 20 62 24 19 30 63
C:
  7: 09 29 62 24 47 33 45 54 55 30 36 27 02
  8: 50 15 20 60 74 06 73 03 10 04 39 11 07 21 64
  9: 61 48 63 01 58 12 65 08 51 19 32 42 18 56 34 23 43
D:
  7: 10 30 64 04 39 36 27 54 55 32 43 50 15
  8: 47 06 45 02 34 48 11 08 24 18 29 62 51 73 03
  9: 63 01 58 12 09 56 33 20 60 74 07 21 65 61 23 42 19
E:
  7: 19 30 63 02 33 45 27 56 61 50 43 48 10
  8: 64 04 39 11 06 74 07 21 09 54 29 60 47 08 51
  9: 36 01 32 42 18 55 03 65 34 23 15 20 62 24 73 58 12
F:
  7: 23 42 74 07 50 43 48 65 62 51 47 33 18
  8: 54 29 61 21 63 27 55 30 09 56 60 19 58 12 10
  9: 11 08 24 73 32 15 20 06 45 01 03 64 04 39 36 02 34
```

For a convenient check of the table, the shared lines contain these
36 distinct codes:

```text
0 5 13 14 16 17 22 25 26 28 31 35 37 38 40 41 44 46
49 52 53 57 59 66 67 68 69 70 71 72 75 76 77 78 79 80
```

Each three-line ending contains exactly the complementary 45 codes:

```text
1 2 3 4 6 7 8 9 10 11 12 15 18 19 20 21 23 24 27 29
30 32 33 34 36 39 42 43 45 47 48 50 51 54 55 56 58 60
61 62 63 64 65 73 74
```

## Optional machine verification

The proof above includes all its data and can be checked directly.
[simple_proof.py](simple_proof.py) reproduces the code table and independently
checks all 72 boards by Cartesian-coordinate enumeration:

```sh
python simple_proof.py --codes
```

To additionally read the five published certificates, verify their 60
symmetry images, and compare every new board against them, run:

```sh
python simple_proof.py --published
```

[SimpleProof.lean](SimpleProof.lean) certifies the same six boards and all
72 distinct images, as well as A's inequality with all 60 published boards,
in Lean's kernel, without a search or external solver:

```sh
lake build SimpleProof
```

A fresh build from the five local Lean modules, without using existing build
artifacts, passed on 22 November 2026. The [build log](simple-lean-build.log)
records the Lean version, source checksums, and theorem axioms. The only
axioms are Lean's standard `propext`, `Classical.choice`, and `Quot.sound`;
there are no unproved placeholders or assumptions about the search software.

Its combined theorem is `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

Here `board0` is A, and `published` enumerates all color permutations and
both orientations of the five supplied representatives. The separate
theorems `TBoards.Simple.at_least_72`, `TBoards.Simple.board0_valid`, and
`TBoards.Simple.board0_not_published` give the numerical bound, validity,
and novelty respectively. This small proof does not require the
17,160-board certificate or its enumeration. The larger result remains
available through `lake build ExtendedCertificates`. Both are lower bounds;
neither asserts the unrestricted exact count.

The six boards are entries 841, 842, 843, 845, 846, and 849 of
[extended_seeds.json](extended_seeds.json), discovered in this workspace.
Their first six rows come from a certificate of Qiyuan Ma,
*Explicit Three- and Four-Color Prismatic T-Tetrominoes* (2026),
DOI 10.5281/zenodo.23631079. The adapted color-table data retain the
source's CC-BY-4.0 attribution; see [the source notices](sources/README.txt).

## What the prior-art check establishes

A literature search on **22 November 2026** found no earlier published
proof that the number of these boards exceeds 60. It covered
[Ma's preprint](https://zenodo.org/records/23631079), its only public
Zenodo version, the latest listed versions of its two cited foundational
papers, and searches under related terminology. The
[prior-art report](PRIOR_ART.md) records the sources, queries, and limitations.

This is a bounded search finding, **not a proof that no previous proof
exists**. The mathematical proof above establishes at least 72 boards and
excludes A from the published 60; absolute historical priority remains
unconfirmed. In particular, an undetermined exact count does not itself
imply that the weaker inequality “more than 60” was previously unresolved.

