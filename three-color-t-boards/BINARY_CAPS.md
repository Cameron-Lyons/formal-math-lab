# At least 10,485,708 three-color T boards

**Theorem.** At least **10,485,708 distinct labeled boards** realize all 81 ordered T patterns exactly once. The 15 groups in the extension add **10,136,748 boards** to the previous 348,960. The original thirteen groups occur unchanged in the combined proof. [Previous proof](SPLICE_PROOF.md) · [Combined Lean theorem](SpliceExtensionCertificates.lean)

The board has ten centered rows of lengths 1, 3, …, 19 and uses colors 0, 1 and 2. A T consists of three consecutive cells in a row and the cell directly above the middle one. Read its colors in the order top, left, middle, right.

## Why a two-color cap is productive

Take the top five rows of lengths 1, 3, 5, 7 and 9. They contain 16 T placements. A binary cap using every binary quadruple once covers exactly the 16 patterns made from 0 and 1. The eleven cells in the next row can then be chosen to make many such caps interchangeable.

For example, use the pivot `22002200222`. Its nine consecutive triples, in order, are

```text
220  200  002  022  220  200  002  022  222
```

Let the cap's last row be a four-bit word, its bitwise complement, and one final bit. The two copies of each repeated triple start four positions apart. One therefore has top 0 and the other top 1. The final bit supplies the top of the unique `222` triple. All nine new patterns contain color 2, so they are disjoint from the 16 binary patterns.

For each fixed final bit the certificate gives **twelve distinct caps** with this property. For example, when the final bit is 0, the following last rows occur with the indicated numbers of caps. The witness file contains all five rows of each cap.

| Last row of cap | Caps | Last row of cap | Caps |
|---|---:|---|---:|
| `000011110` | 1 | `011110000` | 1 |
| `000111100` | 1 | `100001110` | 1 |
| `001111000` | 1 | `101101000` | 1 |
| `010010110` | 3 | `011010010` | 3 |

A second pivot, `22201220122`, places its single `222` triple first. Its other four triples occur in the same order twice. This gives another twelve compatible caps for each choice of the first bit. These two pivots account for groups 7–10 below. The 9 binary-cap groups together contribute **8,234,532 labeled boards**.

## Counting the boards

In each group every cap and pivot realize the same 25 patterns. Every pivot and tail realize the complementary 56. Every recorded cap therefore fits every recorded tail in its group. Reading the pivot and the patterns above it identifies the group, and reading the rows on either side identifies the cap and tail.

Six global color permutations and two horizontal orientations give twelve images per representative. To check that these images are disjoint across the entire family, the proof reads the pivot with the apex color at both ends. The sets of resulting strings for the twelve operations are disjoint across all 28 groups. The operation can therefore be recovered and inverted to recover the representative. [Splice argument](Splice.lean) · [Symmetry argument](SpliceSymmetry.lean)

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

The total is **12 × (29,080 + 844,729) = 10,485,708**. The discovery searches reported exhaustion for each of the fifteen new six-row prefixes. Lean proves the lower bound from the recorded witnesses. The exact number of unrestricted boards remains undetermined.

## Verification and reproduction

The Python audit enumerates T placements in Cartesian coordinates. Expanded mode constructs all 10,485,708 labeled boards, checks all 81 patterns on each, and compares exact base-three encodings for duplicates. The two JSON files supply the previous and new pieces. [Python audit](verify_splice.py) · [Earlier witnesses](splice_witnesses.json) · [Additional witnesses](splice_extension.json)

```sh
python verify_splice.py --with-extension --expand
lake build SpliceExtensionCertificates
```

The expanded audit passed on all 10,485,708 boards. The earlier witness file matches the copy in the 348,960-board archive byte for byte. Lean's kernel reports the standard axioms `propext`, `Classical.choice` and `Quot.sound` for the combined theorem. [Build log](splice-extension-lean-build.log)

Lean checks the new pieces as base-three integers. For neighboring rows encoded as integers `u` and `l`, the rightmost T has code `27 * (u % 3) + (l % 27)`. Dividing both integers by three moves one position left. The proof shows that this scan gives the same patterns as the board definition, including rows with leading zeros. The final theorem constructs an injection from `Fin 10485708` into boards satisfying `TBoards.Valid`. [Packed checker and correctness proof](SplicePacked.lean) · [Final theorem](SpliceExtensionCertificates.lean)

To regenerate the Lean data, run `python prepare_splice_extension.py`. Adding `--build` also checks the proof with at most two group compilers at a time. To replay the discovery search for a group, supply its number from the table. The command below exhausts group 7 and compares its reconstructed caps and tails with the saved lists. Omit the number to replay every extension group.

```sh
python reproduce_splice.py --certificate splice_extension.json --exhaust 7
```

The first six extension groups were found by varying prefixes and selecting compatible caps. The remaining nine groups were selected from binary caps and ternary pivots. The earlier family incorporates data adapted from Qiyuan Ma’s published certificates, distributed under CC-BY-4.0. [Source and license notices](sources/README.txt)
