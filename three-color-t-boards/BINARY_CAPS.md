# At least 10,485,708 three-color T boards

**Theorem.** At least **10,485,708 distinct labeled boards** use all 81 ordered T patterns exactly once. The 15 new groups add **10,136,748 boards** to the [previous 348,960-board proof](SPLICE_PROOF.md), keeping all 13 earlier groups unchanged in the [combined Lean theorem](SpliceExtensionCertificates.lean).

The board has ten centered rows of lengths 1, 3, ..., 19 and uses colors 0, 1, and 2. A T consists of three consecutive cells in one row plus the cell directly above the middle one, read in the order top, left, middle, right.

## Why a two-color cap works so well

Take the top five rows (lengths 1, 3, 5, 7, and 9). They hold 16 T placements. A two-color cap that uses every binary quadruple once covers all 16 patterns made from 0 and 1. We can then choose the 11 cells of the next row so that many such caps become interchangeable.

Take the pivot `22002200222`. Its nine consecutive triples, in order, are:

```text
220  200  002  022  220  200  002  022  222
```

Suppose the cap's bottom row is a four-bit word, followed by its bitwise complement, followed by one last bit. The two copies of each repeated triple start four steps apart, so one gets top 0 and the other gets top 1. The last bit sets the top of the single `222` triple. All nine crossing patterns contain color 2, so none of them collide with the 16 binary patterns.

For each choice of the last bit, the certificate gives **twelve distinct caps** with this property. For example, when the last bit is 0, these bottom rows appear with the counts shown (the witness file stores all five rows of each cap):

| Last row of cap | Caps | Last row of cap | Caps |
|---|---:|---|---:|
| `000011110` | 1 | `011110000` | 1 |
| `000111100` | 1 | `100001110` | 1 |
| `001111000` | 1 | `101101000` | 1 |
| `010010110` | 3 | `011010010` | 3 |

A second pivot, `22201220122`, puts its single `222` triple first and repeats its other four triples in order. That gives another twelve compatible caps for each choice of the first bit. These two pivots form groups 7 to 10 below. Together, the 9 binary-cap groups contribute **8,234,532 labeled boards**.

## Counting the boards

In each group, every cap pairs with the pivot to cover the same 25 patterns, and every tail pairs with the pivot to cover the remaining 56. So any recorded cap fits any recorded tail in its group. Reading the pivot and the patterns above it identifies the group, while the rows above and below the pivot identify the cap and tail.

Six global color permutations and two horizontal orientations give twelve images per representative. To prove that all images are disjoint across the whole family, the proof reads the pivot with the apex color prepended and appended. The sets of resulting strings for the twelve operations are pairwise disjoint across all 28 groups, so we can identify and undo the symmetry to recover the original board (see [Splice.lean](Splice.lean) and [SpliceSymmetry.lean](SpliceSymmetry.lean)).

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

The combined total is **12 × (29,080 + 844,729) = 10,485,708**. The discovery searches exhausted each of the 15 new six-row prefixes. Lean proves the lower bound directly from the recorded witnesses; the exact unrestricted count is still open.

## Verification and reproduction

The [Python audit](verify_splice.py) enumerates T placements in Cartesian coordinates using the [earlier witnesses](splice_witnesses.json) and the [additional witnesses](splice_extension.json). Expanded mode builds all 10,485,708 labeled boards, checks all 81 patterns on each one, and compares exact base-three encodings to verify there are no duplicates.

```sh
python verify_splice.py --with-extension --expand
lake build SpliceExtensionCertificates
```

The expanded audit passed on all 10,485,708 boards. The earlier witness file matches the copy in the 348,960-board archive byte for byte. Lean's kernel reports only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` for the combined theorem (see the [build log](splice-extension-lean-build.log)).

Lean checks the new pieces as base-three integers. For neighboring rows packed as integers `u` and `l`, the rightmost T has code `27 * (u % 3) + (l % 27)`, and dividing both integers by three shifts one position left. [SplicePacked.lean](SplicePacked.lean) proves that this scan extracts the same patterns as the board definition, including rows with leading zeros. [SpliceExtensionCertificates.lean](SpliceExtensionCertificates.lean) then builds an injection from `Fin 10485708` into boards satisfying `TBoards.Valid`.

To regenerate the Lean files, run `python prepare_splice_extension.py` (adding `--build` also checks the proof with at most two group compilers at once). To replay the discovery search for one group, pass its table number; omitting the number replays all 15 extension groups. For example, this command exhausts group 7 and compares its reconstructed caps and tails with the saved lists:

```sh
python reproduce_splice.py --certificate splice_extension.json --exhaust 7
```

The first six extension groups came from varying prefixes and picking compatible caps, and the last nine came from binary caps and ternary pivots. The earlier family uses data adapted from Qiyuan Ma's published certificates, distributed under CC-BY-4.0 (see [source and license notices](sources/README.txt)).
