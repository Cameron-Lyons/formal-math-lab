# More than sixty three-color T boards

**Theorem.** There are at least **72 distinct labeled colorings** of the centered board with row lengths $1,3,\ldots,19$, using colors $0,1,2$, in which each of the $3^4=81$ ordered T patterns occurs once. A T consists of one cell directly above the middle of three consecutive cells. Only translates of this orientation are counted; color names and horizontal reflections count separately.

Write `0 = red`, `1 = green`, and `2 = blue`, and read each pattern in the order (top, left, middle, right).

This shows there are more than 60 valid boards. The proof uses six explicit boards, a finite validity table, and a short symmetry check. Below, we also show directly that board A falls outside all five published families.

## Six boards

Number the rows from 0 at the top to 9 at the bottom, and read each row from left to right. All six boards start with the same seven rows:

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

Attach one of these endings:

| Board | Row 7 | Row 8 | Row 9 |
|---|---|---|---|
| A | `001022002021212` | `10110022000210001` | `1202021011020120100` |
| B | `002011000212101` | `10202202100020012` | `1200101102120220100` |
| C | `100220200010002` | `21202020101102101` | `0210011022012002121` |
| D | `101011000012120` | `20200210220022010` | `1001100202021021201` |
| E | `201002000212101` | `10110202100020220` | `1001200102120220110` |
| F | `212021210220200` | `00021000100201101` | `1022012020010110021` |

Each row has the required length, giving six 100-cell boards.

## Every pattern occurs exactly once

Write $a_r(j)$ for entry $j$ of row $r$, indexed from 0. That cell sits at $(j-r,-r)$, so every translated T has the form

$$
W_{r,j}=\bigl(a_{r-1}(j),a_r(j),a_r(j+1),a_r(j+2)\bigr),
\qquad 1\le r\le9,\quad 0\le j\le2r-2.
$$

The lower middle cell lies at $(j+1-r,-r)$, and the top cell shares its horizontal coordinate. The three lower cells stay inside row $r$ exactly for $0\le j\le 2r-2$, which keeps the top cell inside row $r-1$. In the other direction, any T is determined by its lower row $r$ and its leftmost lower cell $j$. So this lists all placements once each, and there are

$$
1+3+5+\cdots+17=81
$$

placements in total. Encode an ordered color pattern in base three as

$$
E(t,l,m,u)=27t+9l+3m+u.
$$

This maps the 81 color patterns bijectively to $0,\ldots,80$. The table below lists $E(W_{r,j})$ from left to right for every row. For each of the six boards, the six shared lines plus its three own lines contain every integer from 0 to 80 once. All six boards are therefore valid.

For instance, board A's first window in row 7 is $(0,0,0,1)$, which has code 1, and its first window in row 8 is $(0,1,0,1)$, with code 10.

## Why these give 72 different boards

Permuting the three colors preserves validity because it permutes the 81 ordered patterns bijectively. Reflecting every row also preserves validity: it permutes the T placements and turns each pattern $(t,l,m,u)$ into $(t,u,m,l)$. So each of the six boards produces $3!\cdot2=12$ valid symmetry images (before checking for duplicates).

We now check that all 72 images are distinct. Suppose two images are equal. Undoing one transformation turns one of the six boards into another by a color permutation, possibly followed by a reflection.

A reflection cannot happen. Every one of the six boards has row 2 equal to `21121`, where entries 0 and 2 differ. In the reversed row `12112`, entries 0 and 2 are equal, and a color permutation cannot make equal entries unequal. So no recolored reflection can match row 2.

Without reflection, the color permutation must fix 0 (from the apex cell) and also fix 2 and 1 (from entries 0 and 1 of row 2). It must be the identity. Finally, the six boards themselves are distinct because row 7 begins with `001`, `002`, `100`, `101`, `201`, and `212`.

Two images therefore agree only when they come from the same board and the same transformation. That gives at least $6\cdot12=72>60$ valid boards. **QED.**

## Board A is outside all five published families

This also answers the specific request for a new board. The five published representatives in [the supplied certificate](sources/anc/certificates.json) all have apex color 0 and split into two groups (rows numbered from 0):

| Published representatives | Row 2 | Row 6 |
|---|---|---|
| Three representatives | `00100` | Not needed |
| The other two representatives | `21121` | `0201201111202` |
| Board A | `21121` | `0120111221110` |

Suppose a recoloring of a published representative, with or without reflection, produced board A. Matching the apex forces the recoloring to fix color 0. The three representatives in the first group contain zeros in row 2, while board A has none, so they cannot produce A even after reflection.

For the other two representatives, reflecting row 2 gives `12112`. Its entries 0 and 2 match, whereas those entries in A's `21121` differ, and recoloring cannot change that. Without reflection, matching row 2 fixes colors 1 and 2 as well, leaving only the identity. Row 6 then disagrees with A's row 6, ruling out those two representatives too.

Board A is therefore unequal to **every one of the 60 published boards**. Since the code table checks that A is valid, board A together with the published 60 already proves more than 60 boards exist. The six-board proof above gives the stronger bound of 72 without depending on the published count.

## Complete finite check

The numbers below are decimal codes; leading zeros are only for alignment. The shared block applies to all six boards A through F.

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

To make checking easier, the shared lines contain these 36 distinct codes:

```text
0 5 13 14 16 17 22 25 26 28 31 35 37 38 40 41 44 46
49 52 53 57 59 66 67 68 69 70 71 72 75 76 77 78 79 80
```

Each three-line ending contains the remaining 45 codes:

```text
1 2 3 4 6 7 8 9 10 11 12 15 18 19 20 21 23 24 27 29
30 32 33 34 36 39 42 43 45 47 48 50 51 54 55 56 58 60
61 62 63 64 65 73 74
```

## Optional machine verification

The proof above contains all its data and can be checked by hand. [simple_proof.py](simple_proof.py) reproduces the code table and checks all 72 boards independently using Cartesian coordinates:

```sh
python simple_proof.py --codes
```

To also read the five published certificates, verify their 60 symmetry images, and compare every new board against them:

```sh
python simple_proof.py --published
```

[SimpleProof.lean](SimpleProof.lean) checks the same six boards, all 72 distinct images, and A's inequality with all 60 published boards inside Lean's kernel, with no search or external solver:

```sh
lake build SimpleProof
```

A clean build from the five local Lean modules, without cached build files, passed on 22 November 2026. The [build log](simple-lean-build.log) lists the Lean version, source checksums, and theorem axioms. Only Lean's standard axioms (`propext`, `Classical.choice`, and `Quot.sound`) appear, with no `sorry`s or assumptions about search software.

The combined theorem is `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

Here `board0` is A, and `published` lists all color permutations and both orientations of the five published representatives. The individual theorems `TBoards.Simple.at_least_72`, `TBoards.Simple.board0_valid`, and `TBoards.Simple.board0_not_published` prove the bound, validity, and novelty separately. This small proof does not depend on the 17,160-board certificate or its search. The larger proof is still available via `lake build ExtendedCertificates`. Both are lower bounds; neither determines the exact unrestricted count.

The six boards are entries 841, 842, 843, 845, 846, and 849 of [extended_seeds.json](extended_seeds.json), found in this workspace. Their first six rows come from a certificate of Qiyuan Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes* (2026), DOI 10.5281/zenodo.23631079. The adapted color-table data keep the source's CC-BY-4.0 attribution; see [the source notices](sources/README.txt).

## What the prior-art check establishes

A literature search on **22 November 2026** found no earlier published proof that more than 60 of these boards exist. It checked [Ma's preprint](https://zenodo.org/records/23631079), its only public Zenodo version, the latest listed versions of its two cited foundational papers, and related search terms. See the [prior-art report](PRIOR_ART.md) for the exact sources, queries, and limits of the search.

This is a bounded search finding, **not a proof that no earlier proof exists**. The mathematical proof above shows at least 72 boards and rules out board A from the published 60, while absolute historical priority remains unconfirmed. Even though the exact count is unknown, that alone does not mean the weaker inequality "more than 60" was previously open.
