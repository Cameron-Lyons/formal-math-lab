# At least 21,158,736 three-color T boards

This layer more than doubles the [previous 10,485,708-board lower bound](BINARY_CAPS.md), pushing the certified count past **21 million** valid labeled boards. Three extensions drive the gain: new high-tail asymmetric pivots, **palindromic pivots** (which require a richer symmetry identifier and careful reflection deduplication), and **tail transfer** (reusing already-discovered tails under slightly modified pivots without running a new search).

**Theorem.** There are at least **21,158,736 distinct labeled boards**, forming **1,763,228 distinct orbits** of size 12 under global color permutation and horizontal reflection. This adds **10,673,028 boards** to the previous certificate, proved in the [combined Lean theorem](SpliceFurtherCertificates.lean). The exact unrestricted count remains open.

| Family | Groups | Orbit representatives | Labeled boards |
|---|---:|---:|---:|
| Previous certificate | 28 | 873,809 | 10,485,708 |
| New groups with asymmetric pivots | 28 | 747,740 | 8,972,880 |
| New groups with palindromic pivots | 69 | 130,272 | 1,563,264 |
| Groups reusing earlier tails | 185 | 11,407 | 136,884 |
| **Total** | **310** | **1,763,228** | **21,158,736** |

## How the count works

As before, the board has ten centered rows of lengths $1, 3, \ldots, 19$, and each upright T reads one top cell followed by the three consecutive cells directly below it from left to right. A valid board covers all $3^4 = 81$ ordered quadruples across its 81 placements.

Fixing row 5 (the 11-cell **pivot**) splits the board cleanly into a 5-row **cap** above (covering 25 patterns with the pivot) and a 4-row **tail** below (covering the remaining 56 patterns). Each group fixes a pivot and a 25-pattern set so that every recorded cap fits every recorded tail (see [Splice.lean](Splice.lean) and the [new explicit groups](splice_further.json)).

For example, changing a single digit from pivot `22220110022` to `22221110022` preserves the exact same six compatible caps. Those two groups have 25,209 and 25,117 tails, yielding

$$
12 \times 6 \times (25{,}209 + 25{,}117) = \mathbf{3{,}623{,}472}\text{ labeled boards}
$$

from just two pivots. Every complete board uniquely determines its pivot, its 25 upper patterns, and all of its rows.

### Counting reflections at a palindromic pivot

The new explicit families include **3 palindromic pivots** — row-5 strings that read the same forward and backward. Why does a palindromic pivot break the earlier symmetry argument? In the 10-million-board proof, Lean identified which of the 12 symmetries produced a board by reading the 13-digit tag `apex + pivot + apex`. When the pivot is a palindrome, horizontal reflection leaves that tag *unchanged*, so the tag can no longer distinguish a board from its left-right mirror image.

To solve this, the new proof reads **all six upper rows** (rows 0–5) for every group. Because every cap recorded here has at least one non-palindromic row, a finite lookup table in [SplicePrefixData.lean](SplicePrefixData.lean) uniquely identifies which of the 12 symmetries produced each transformed 6-row prefix, and [SplicePrefixSymmetry.lean](SplicePrefixSymmetry.lean) checks all 12 operations on every recorded cap inside Lean. Two equal output boards must therefore arise from the same symmetry, which can be inverted to recover the unique original representative.

A subtle bonus occurs when the **25-pattern set** at a palindromic pivot is itself mirror-invariant. For example, at pivot `22002020022`, one upper pattern set is unchanged by horizontal reflection, so its compatible caps come in mirror-image pairs and its compatible tails are closed under reflection:

* To avoid double-counting under reflection, we keep **one cap from each reflected pair** (2 cap representatives) and take the union of all discovered tails with their reflections.
* Out of 5,000 discovered tails, 2,318 already appear in the reflected list, so the union contains $5{,}000 + 5{,}000 - 2{,}318 = 7{,}682$ distinct tails.
* Multiplying by 2 caps and 12 symmetries yields $12 \times 2 \times 7{,}682 = 184{,}368$ labeled boards.

A deterministic sample at the palindromic pivot `22012221022` adds another **198,984 boards** from 62 binary-cap pattern sets and 12,235 explicit tails (replayable with [reproduce_symmetric.py](reproduce_symmetric.py)).

### Reusing tails under a different pivot

Changing the pivot (row 5) only alters the T placements that touch row 5 — the 9 placements between rows 4 and 5, and the 11 placements between rows 5 and 6. All 45 T placements inside rows 6–9 stay completely unchanged! Whenever a modified pivot combines with a subset of an earlier group's tails and a new cap list to partition the 81 quadruples cleanly, we can **transfer** those tails into a brand-new group at almost zero search cost.

In one transfer, 299 tails originally found for pivot `22111212222` also fit 4 caps at pivot `22111212221`, adding $12 \times 4 \times 299 = 14{,}352$ labeled boards. Each entry in [splice_transfer.json](splice_transfer.json) names an earlier source group and lists which indices to copy from its sorted tail list. [SpliceTransfer.lean](SpliceTransfer.lean) checks each transferred group, and the combined theorem verifies that every one of the 310 groups has a distinct `(pivot, upper pattern set)` pair.

## Checking the result

From this directory, run these commands to verify the four-layer Lean theorem and independently expand the entire certificate:

```sh
lake build SpliceFurtherCertificates
python verify_splice.py --through-transfer --expand --jobs 3
```

The [independent Python checker](verify_splice.py) enumerates T placements from Cartesian coordinates, checks all 81 patterns on every labeled board, and compares exact base-3 encodings within each pivot orbit to rule out duplicates. The [expanded audit](splice-further-audit.log) passed on all 21,158,736 images and confirmed that the original 17,160 boards appear inside the family. The [Lean build log](splice-further-lean-build.log) lists the axioms Lean reported.

Regenerating the 286 new Lean source files from the four JSON witness files reproduced them byte for byte. The discovery replay accepts one-based group numbers from `splice_further.json`: group 18 checks the reflected-tail union above, and group 27 checks one of the sampled binary-cap families. The discovery searches used a mix of exhaustive runs, fixed limits, and chosen samples, while the Lean theorem relies strictly on the recorded witnesses.

```sh
python prepare_splice_extension.py --further
python reproduce_splice.py --certificate splice_further.json 18 27
```

The reverse search also reproduces the transfer descriptors exactly via `python prepare_splice_transfer.py --discover`. Both earlier splice witness files stay unchanged. The starting family incorporates data adapted from Qiyuan Ma's published certificates (see the [previous proof](BINARY_CAPS.md) and [source and license notices](sources/README.txt)).
