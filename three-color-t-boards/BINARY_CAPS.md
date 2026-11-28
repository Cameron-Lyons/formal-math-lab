# At least 10,485,708 three-color T boards

In the [348,960-board splicing proof](SPLICE_PROOF.md), we saw that if $C$ top caps all share the same 25 upper T patterns with a fixed row-5 pivot, they pair freely with every compatible tail to produce $12 \cdot C \cdot T$ boards. The big leap to over **10 million** boards comes from designing **two-color (binary) caps** paired with periodic three-color pivots so that up to **12 distinct caps** become completely interchangeable.

**Theorem.** At least **10,485,708 distinct labeled boards** use all 81 ordered T patterns exactly once. The 15 new groups add **10,136,748 boards** to the [previous 348,960-board proof](SPLICE_PROOF.md), keeping all 13 earlier groups unchanged in the [combined Lean theorem](SpliceExtensionCertificates.lean).

As before, the board has ten centered rows of lengths $1, 3, \ldots, 19$ colored with `0`, `1`, and `2`, and each upright T reads one top cell followed by the three consecutive cells directly beneath it (top, left, middle, right).

## Why a two-color cap works so well

Look at the top five rows (rows 0–4, lengths $1, 3, 5, 7, 9$). They contain exactly $1 + 3 + 5 + 7 = 16$ internal T placements. If we restrict a cap to just **two colors** (`0` and `1`), there are only $2^4 = 16$ possible binary quadruples — so **every** valid binary cap automatically covers the exact same 16 internal patterns, namely $\{0, 1\}^4$!

Now we choose the 11-cell pivot (row 5) so that two magical things happen simultaneously:

1. **Zero collisions with the cap:** every three-cell slice of the pivot contains at least one color `2`. All nine crossing T patterns across row 5 therefore include color `2`, so none can ever collide with the 16 binary patterns inside the cap.
2. **Repeated slices make caps interchangeable:** design the pivot's triples to repeat with period 4.

Take the pivot `22002200222`. Its nine consecutive triples, from left to right, are:

```text
220  200  002  022  |  220  200  002  022  |  222
```

The first four triples repeat identically four steps later, followed by the single triple `222`. Now pick any binary cap whose bottom row (row 4, length 9) has the form

$$
b_0 b_1 b_2 b_3 \; \bar{b}_0 \bar{b}_1 \bar{b}_2 \bar{b}_3 \; b_8,
$$

a 4-bit word followed by its bitwise complement ($\bar{b}_i = 1 - b_i$), followed by one last bit $b_8$. Look at what happens to the nine crossing T patterns:

* Each repeated triple (`220`, `200`, `002`, `022`) appears once beneath $b_i$ and once beneath $\bar{b}_i$. Whether $b_i$ is `0` or `1`, that triple receives **both** top colors `0` and `1` — producing the fixed set of 8 patterns `0220, 1220, 0200, 1200, 0002, 1002, 0022, 1022`.
* The final triple `222` gets top color $b_8$, producing `(b_8)222`.

Every binary cap with this row-4 shape and the same final bit $b_8$ therefore generates the **exact same 25 upper patterns** (all 16 binary patterns plus these 9 crossing patterns)!

For each choice of the last bit $b_8 \in \{0, 1\}$, the certificate contains **twelve distinct binary caps** with this property. For example, when $b_8 = 0$, these eight bottom rows appear with the multiplicities shown (the witness file stores all five rows of every cap; `010010110` and `011010010` each admit three different valid binary fillings of rows 0–3):

| Last row of cap | Caps | Last row of cap | Caps |
|---|---:|---|---:|
| `000011110` | 1 | `011110000` | 1 |
| `000111100` | 1 | `100001110` | 1 |
| `001111000` | 1 | `101101000` | 1 |
| `010010110` | 3 | `011010010` | 3 |

A second pivot, `22201220122`, places the single `222` triple first and repeats its remaining four triples (`220, 201, 012, 122`) in order. That yields another **twelve** compatible binary caps for each choice of the *first* bit of row 4. These two pivots produce groups 7 through 10 below. Together, the 9 binary-cap groups (groups 7–15) contribute **8,234,532 labeled boards**.

## Counting the boards

Within each group, every listed cap pairs with the pivot to cover the same 25 patterns, and every listed tail pairs with the pivot to cover the complementary 56 patterns — so every cap fits every tail validly. Reading the pivot and the 25 patterns above it identifies the group uniquely, while rows 0–4 and 6–9 identify the cap and tail.

As in the earlier proof, six global color permutations and two horizontal orientations yield twelve images per representative. To prove that all twelve images are pairwise disjoint across the entire 28-group family, Lean reads the 13-digit tag formed by prepending and appending the apex color to the pivot (`apex + pivot + apex`). The sets of tags produced by the twelve symmetry operations are pairwise disjoint across all 28 groups, so any labeled board uniquely reveals which symmetry produced it; inverting that symmetry recovers the original representative (see [Splice.lean](Splice.lean) and [SpliceSymmetry.lean](SpliceSymmetry.lean)).

| Extension group | Pivot | Caps | Tails | Representatives |
|---:|---|---:|---:|---:|
| 1 | `22111212122` | 4 | 2,105 | 8,420 |
| 2 | `22011212222` | 4 | 2,496 | 9,984 |
| 3 | `22112112222` | 4 | 1,997 | 7,988 |
| 4 | `10010121110` | 6 | 3,729 | 22,374 |
| 5 | `22111212222` | 4 | 7,211 | 28,844 |
| 6 | `22102110022` | 4 | 20,227 | 80,908 |
| 7 | `22002200222` | 12 | 8,399 | 100,788 |
| 8 | `22201220122` | 12 | 9,405 | 112,860 |
| 9 | `22002200222` | 12 | 10,150 | 121,800 |
| 10 | `22201220122` | 12 | 9,280 | 111,360 |
| 11 | `22220122022` | 8 | 8,849 | 70,792 |
| 12 | `22221022122` | 8 | 8,426 | 67,408 |
| 13 | `21221122121` | 11 | 4,173 | 45,903 |
| 14 | `12221122112` | 8 | 2,815 | 22,520 |
| 15 | `22122120122` | 5 | 6,556 | 32,780 |
| **Extension total** | | **114** | **105,818** | **844,729** |

Combining the 13 earlier groups and 15 new groups gives **$12 \times (29{,}080 + 844{,}729) = 10{,}485{,}708$** distinct valid labeled boards. The discovery searches exhausted each of the 15 new six-row prefixes. Lean proves the lower bound directly from the recorded witnesses; the exact unrestricted count remains open.

## Verification and reproduction

The [Python audit](verify_splice.py) enumerates T placements in Cartesian coordinates using the [earlier witnesses](splice_witnesses.json) and the [additional witnesses](splice_extension.json). Expanded mode builds all 10,485,708 labeled boards, checks all 81 patterns on each one, and compares exact base-3 encodings to verify there are no duplicates.

```sh
python verify_splice.py --with-extension --expand
lake build SpliceExtensionCertificates
```

The expanded audit passed on all 10,485,708 boards, and the earlier witness file matches the copy in the 348,960-board archive byte for byte. Lean's kernel reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for the combined theorem (see the [build log](splice-extension-lean-build.log)).

**How Lean checks 105,818 tails quickly.** Rather than storing each row as a list of digits, Lean packs every row as a single base-3 natural number (rightmost cell in the units place). For two neighboring packed rows `u` (upper) and `l` (lower):

* `u % 3` extracts the rightmost top cell, and `l % 27` extracts the base-3 code of the rightmost three lower cells.
* Thus `27 * (u % 3) + (l % 27)` equals the exact base-3 pattern code of the rightmost T between those rows.
* Integer-dividing both `u` and `l` by 3 shifts the T window one position left.

[SplicePacked.lean](SplicePacked.lean) proves this arithmetic scan extracts the exact same patterns as the geometric board definition, including rows with leading zeros. [SpliceExtensionCertificates.lean](SpliceExtensionCertificates.lean) then constructs an explicit injection from `Fin 10485708` into boards satisfying `TBoards.Valid`.

To regenerate the Lean files, run `python prepare_splice_extension.py` (adding `--build` also checks the proof with at most two group compilers at once). To replay the discovery search for one group, pass its table number; omitting the number replays all 15 extension groups. For example, this command exhausts group 7 and compares its reconstructed caps and tails with the saved lists:

```sh
python reproduce_splice.py --certificate splice_extension.json --exhaust 7
```

The first six extension groups came from varying prefixes and picking compatible caps, and the last nine came from binary caps and ternary pivots. The earlier family uses data adapted from Qiyuan Ma's published certificates, distributed under CC-BY-4.0 (see [source and license notices](sources/README.txt)).
