# More than sixty three-color T boards

Consider a 10-row triangular pyramid (the **ziggurat** $Z_9$) of 100 unit cells, with centered rows of lengths $1, 3, 5, \ldots, 19$. Color each cell with one of three colors (`0` = red, `1` = green, `2` = blue), and examine every upright **T-tetromino** — one top cell $t$ sitting directly above the middle of three consecutive cells $l, m, u$ in the row below:

```text
      t
    l m u
```

Only translates of this single upright orientation are counted, and each pattern is read in the order $(t, l, m, u)$ (top, left, middle, right). There are $81$ placements on the board and $3^4 = 81$ possible color patterns, so a board is **valid** when every pattern appears exactly once. Qiyuan Ma's founding paper exhibited 60 labeled boards (5 symmetry families of 12). Here we give a short, completely self-contained proof that strictly more than 60 valid boards exist.

**Theorem.** There are at least **72 distinct labeled colorings** of the centered board with row lengths $1, 3, \ldots, 19$, using colors $0, 1, 2$, in which each of the $3^4 = 81$ ordered T patterns occurs once. Color names and horizontal reflections are counted separately.

**Proof roadmap.** The proof requires no computer search and does not rely on Ma's 60-board list:

1. **Six explicit boards (A through F)** all share the same first seven rows and differ only in their bottom three rows.
2. **A finite pattern check** translates each of the 81 T windows into a base-3 integer from $0$ to $80$ and confirms every integer appears once on each board.
3. **A short symmetry check** applies the 6 color permutations and horizontal reflection ($6 \cdot 2 = 12$ valid transformations) to each board and proves that all $6 \cdot 12 = 72$ resulting boards are distinct, inspecting only the apex, row 2, and the first three cells of row 7.

After proving the theorem, we also show directly — using just three rows — that board A lies outside all 60 published boards.

## Six explicit boards

Number the rows from $0$ at the top to $9$ at the bottom, and read each row from left to right. All six boards begin with the same seven rows (centered one above the next):

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

Attach any one of the six three-row endings below to complete the board:

| Board | Row 7 | Row 8 | Row 9 |
|---|---|---|---|
| A | `001022002021212` | `10110022000210001` | `1202021011020120100` |
| B | `002011000212101` | `10202202100020012` | `1200101102120220100` |
| C | `100220200010002` | `21202020101102101` | `0210011022012002121` |
| D | `101011000012120` | `20200210220022010` | `1001100202021021201` |
| E | `201002000212101` | `10110202100020220` | `1001200102120220110` |
| F | `212021210220200` | `00021000100201101` | `1022012020010110021` |

Every row $r$ has length $2r + 1$, giving six 100-cell boards.

## Step 1: Every pattern occurs exactly once

Write $a_r(j)$ for entry $j$ of row $r$ (indexed from $0$). Placing cell $a_r(j)$ at integer coordinates $(j - r, -r)$ centers row $r$ horizontally around $x = 0$. Every translated upright T-tetromino then takes the form

$$
W_{r,j} = \bigl(a_{r-1}(j),\, a_r(j),\, a_r(j+1),\, a_r(j+2)\bigr),
\qquad 1 \le r \le 9,\quad 0 \le j \le 2r - 2.
$$

Why does this list every placement once and only once? The lower middle cell $a_r(j+1)$ sits at $(j + 1 - r, -r)$, and the top cell $a_{r-1}(j)$ sits directly above it at $(j - (r - 1), -(r - 1)) = (j + 1 - r, -r + 1)$. The three lower cells lie inside row $r$ (length $2r + 1$) precisely when $0 \le j \le 2r - 2$, which simultaneously keeps the top cell inside row $r - 1$ (length $2r - 1$). Conversely, every T is uniquely determined by its lower row $r$ and leftmost lower index $j$. Thus there are

$$
1 + 3 + 5 + \cdots + 17 = 81
$$

placements in total.

To check that all 81 placements carry distinct color quadruples, encode each pattern $(t, l, m, u)$ as a 4-digit base-3 integer:

$$
E(t, l, m, u) = 27t + 9l + 3m + u.
$$

This maps the 81 ordered patterns bijectively onto $\{0, 1, \ldots, 80\}$. The [Complete finite check](#complete-finite-check) below lists $E(W_{r,j})$ from left to right for every row. Let us sanity-check a few entries by hand:

* In row 1, the sole window is $(a_0(0), a_1(0), a_1(1), a_1(2)) = (0, 0, 0, 0)$, giving code $0$.
* In row 2, the first window is $(a_1(0), a_2(0), a_2(1), a_2(2)) = (0, 2, 1, 1)$, giving $0 + 18 + 3 + 1 = 22$.
* On board A, the first window in row 7 is $(0, 0, 0, 1)$, which has code $1$, and the first window in row 8 is $(0, 1, 0, 1)$, with code $9 + 1 = 10$.

For each of the six boards, the six shared lines (36 codes) together with its three individual ending lines (45 codes) contain every integer from $0$ to $80$ once. Hence all six boards are valid.

## Step 2: Why these give 72 different boards

Two global symmetries preserve validity:

* **Color permutations ($3! = 6$ ways):** relabeling $\{0, 1, 2\}$ permutes the 81 ordered patterns bijectively.
* **Horizontal reflection ($2$ orientations):** reversing every row permutes the 81 T placements bijectively while mapping each pattern $(t, l, m, u)$ to $(t, u, m, l)$, which is also a bijection on the 81 patterns.

Combining the two gives $3! \cdot 2 = 12$ valid symmetry images per board (72 images in all before checking for duplicates).

We now verify that all 72 images are pairwise distinct. Suppose two images coincide. Applying the inverse of one transformation turns one of the six boards into another via a single color permutation, possibly followed by a horizontal reflection.

1. **No reflection can occur.** Every one of the six boards has row 2 equal to `21121`, where entry $0$ (`2`) and entry $2$ (`1`) are *different*. In the reflected row `12112`, entry $0$ (`1`) and entry $2$ (`1`) are *equal*. Since a color permutation is a bijection, it can never turn equal entries into unequal ones, so no recolored reflection of row 2 can equal `21121`.
2. **No nontrivial color permutation can occur.** Without reflection, matching the apex (row 0, `0`) forces the permutation to fix `0`. Matching entries $0$ and $1$ of row 2 (`21121`) forces it to fix `2` and `1` as well. The color permutation must therefore be the identity.
3. **The six boards themselves are distinct.** Their row 7 entries begin with six different triples: `001` (A), `002` (B), `100` (C), `101` (D), `201` (E), and `212` (F).

Consequently, two images agree only when they come from the same board and the same transformation. This yields at least $6 \cdot 12 = 72 > 60$ distinct valid boards. **QED.**

## Board A is outside all five published families

The same quick inspection also answers the direct question of whether a valid board exists outside the 60 published ones. The five published representatives in [the supplied certificate](sources/anc/certificates.json) all have apex color `0` and fall into two groups (rows numbered from $0$):

| Published representatives | Row 2 | Row 6 |
|---|---|---|
| Three representatives | `00100` | Not needed |
| The other two representatives | `21121` | `0201201111202` |
| Board A | `21121` | `0120111221110` |

Suppose a color permutation of a published representative, with or without horizontal reflection, produced board A:

* Matching the apex (`0` in every board) forces the color permutation to fix color `0`.
* **First group (three representatives):** their row 2 (`00100`) contains zeros, whereas board A's row 2 (`21121`) contains none. Because color `0` is fixed and reflection preserves the number of zeros, none of these three can produce A.
* **Second group (two representatives):** reflecting row 2 (`21121`) yields `12112`, whose entries $0$ and $2$ match while board A's differ — ruling out reflection. Without reflection, matching row 2 fixes colors `1` and `2` as well, leaving only the identity transformation. Row 6 then disagrees (`0201201111202` vs. `0120111221110`), ruling out these two representatives too.

Board A is therefore unequal to **every one of the 60 published boards**. Since the code table confirms A is valid, board A together with the 60 published boards already establishes $> 60$ valid boards; the six-board proof above proves the stronger bound of 72 completely independently of the published list.

## Complete finite check

The numbers below are decimal base-3 pattern codes $E(W_{r,j})$ listed from left to right (leading zeros are for column alignment only). The shared block applies to all six boards A through F.

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

Sorted for easy hand checking, the six shared lines contain these **36 distinct codes**:

```text
0 5 13 14 16 17 22 25 26 28 31 35 37 38 40 41 44 46
49 52 53 57 59 66 67 68 69 70 71 72 75 76 77 78 79 80
```

Each three-line ending contains the exact remaining **45 codes**:

```text
1 2 3 4 6 7 8 9 10 11 12 15 18 19 20 21 23 24 27 29
30 32 33 34 36 39 42 43 45 47 48 50 51 54 55 56 58 60
61 62 63 64 65 73 74
```

## Optional machine verification

Although every line of the proof can be checked by hand, two independent mechanized verifications are provided.

First, [simple_proof.py](simple_proof.py) reproduces the code table and checks all 72 boards independently using Cartesian coordinates:

```sh
python simple_proof.py --codes
```

To also read the five published certificates, verify their 60 symmetry images, and confirm every new board lies outside them:

```sh
python simple_proof.py --published
```

Second, [SimpleProof.lean](SimpleProof.lean) checks the same six boards, all 72 distinct images, and A's inequality against all 60 published boards inside Lean's kernel, with no search or external solver:

```sh
lake build SimpleProof
```

A clean build from the five local Lean modules, without cached build files, passed on 22 November 2026. The [build log](simple-lean-build.log) lists the Lean version, source checksums, and theorem axioms. Only Lean's standard axioms (`propext`, `Classical.choice`, and `Quot.sound`) appear, with no `sorry`s or assumptions about search software.

The combined theorem is `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

Here `board0` is A, and `published` lists all color permutations and both orientations of the five published representatives. The individual theorems `TBoards.Simple.at_least_72`, `TBoards.Simple.board0_valid`, and `TBoards.Simple.board0_not_published` prove the bound, validity, and novelty separately. This small proof does not depend on the 17,160-board certificate or its search. The larger proof remains available via `lake build ExtendedCertificates`. Both are lower bounds; neither determines the exact unrestricted count.

The six boards are entries 841, 842, 843, 845, 846, and 849 of [extended_seeds.json](extended_seeds.json), found in this workspace. Their first six rows come from a certificate of Qiyuan Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes* (2026), DOI 10.5281/zenodo.23631079. The adapted color-table data keep the source's CC-BY-4.0 attribution; see [the source notices](sources/README.txt).

## What the prior-art check establishes

A literature search on **22 November 2026** found no earlier published proof that more than 60 of these boards exist. It checked [Ma's preprint](https://zenodo.org/records/23631079), its only public Zenodo version, the latest listed versions of its two cited foundational papers, and related search terms. See the [prior-art report](PRIOR_ART.md) for the exact sources, queries, and limits of the search.

This is a bounded search finding, **not a proof that no earlier proof exists**. The mathematical proof above shows at least 72 boards and rules out board A from the published 60, while absolute historical priority remains unconfirmed. Even though the exact count is unknown, that alone does not mean the weaker inequality "more than 60" was previously open.
