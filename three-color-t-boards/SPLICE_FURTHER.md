# At least 21,158,736 three-color T boards

There are at least **21,158,736 distinct labeled boards**, forming **1,763,228 distinct orbits** under color permutation and horizontal reflection. This adds **10,673,028 boards** to the [previous 10,485,708-board certificate](BINARY_CAPS.md), proved in the [combined Lean theorem](SpliceFurtherCertificates.lean). The exact unrestricted count is still open.

| Family | Groups | Orbit representatives | Labeled boards |
|---|---:|---:|---:|
| Previous certificate | 28 | 873,809 | 10,485,708 |
| New groups with asymmetric pivots | 28 | 747,740 | 8,972,880 |
| New groups with palindromic pivots | 69 | 130,272 | 1,563,264 |
| Groups reusing earlier tails | 185 | 11,407 | 136,884 |
| **Total** | **310** | **1,763,228** | **21,158,736** |

## How the count works

A board has ten centered rows of lengths 1, 3, ..., 19. Each ordered T pattern reads the top cell followed by the three cells below it from left to right. There are 81 placements and 81 possible ordered quadruples, so a valid board uses each quadruple once.

Fix the eleven cells of row 5 as the pivot. The five rows above it form a cap and pair with the pivot to cover 25 patterns; the four rows below form a tail and pair with the pivot to cover the other 56. A group lists caps and tails with those fixed pattern sets, so any cap pairs with any tail (see [Splice.lean](Splice.lean) and the [new explicit groups](splice_further.json)). For instance, changing one digit from pivot `22220110022` to `22221110022` keeps the same six compatible caps. Those two groups have 25,209 and 25,117 tails, giving 12 × 6 × (25,209 + 25,117) = **3,623,472 labeled boards**. Every full board determines its pivot, its upper pattern set, and all of its rows.

### Counting reflections at a palindromic pivot

The new explicit families include 3 palindromic pivots, which horizontal reflection leaves unchanged. Because the earlier apex-and-pivot tag gives the same marker in both orientations here, the new proof reads all six upper rows for every group. A finite table in [SplicePrefixData.lean](SplicePrefixData.lean) identifies which symmetry produced each transformed prefix, and [SplicePrefixSymmetry.lean](SplicePrefixSymmetry.lean) checks all twelve operations on every recorded cap in Lean. Equal output boards must come from the same operation, which can then be inverted.

For example, one upper pattern set at pivot `22002020022` is invariant under reflection. We keep one cap from each reflected pair and include the reflected tails in the tail list. Out of 5,000 discovered tails, 2,318 also appear in the reflected list, so their union gives 2 cap representatives and 7,682 distinct tails, or 184,368 labeled boards. A deterministic sample at `22012221022` adds another 198,984 boards from 62 binary-cap pattern sets and 12,235 explicit tails (replayable with [reproduce_symmetric.py](reproduce_symmetric.py)).

### Reusing tails under a different pivot

Changing the pivot only alters the T placements that touch row 5. Lower rows can be reused whenever the new upper and lower pattern sets still partition the 81 quadruples. In one transfer, 299 tails from pivot `22111212222` also fit 4 caps at pivot `22111212221`, adding 14,352 labeled boards. Each entry in [splice_transfer.json](splice_transfer.json) names an earlier group and lists which indices to take from its sorted tail list. [SpliceTransfer.lean](SpliceTransfer.lean) checks each transferred group, and the combined theorem verifies that every group has a distinct pivot and upper pattern set.

## Checking the result

From this directory, run these commands to check the four-layer Lean theorem and independently expand the full certificate:

```sh
lake build SpliceFurtherCertificates
python verify_splice.py --through-transfer --expand --jobs 3
```

The [independent Python checker](verify_splice.py) enumerates T placements from Cartesian coordinates, checks all 81 patterns on every labeled board, and compares exact base-three encodings within each pivot orbit to rule out duplicates. The [expanded audit](splice-further-audit.log) passed on all 21,158,736 images and confirmed that the original 17,160 boards appear in the family. The [Lean build log](splice-further-lean-build.log) lists the axioms Lean reported.

Regenerating the 286 new Lean source files from the four JSON witness files reproduced them byte for byte. The discovery replay takes one-based group numbers from `splice_further.json`: group 18 checks the reflected-tail union above, and group 27 checks one of the sampled binary-cap families. The searches used a mix of exhaustive runs, fixed limits, and chosen samples, while the Lean theorem relies only on the recorded witnesses.

```sh
python prepare_splice_extension.py --further
python reproduce_splice.py --certificate splice_further.json 18 27
```

The reverse search also reproduces the transfer descriptors exactly via `python prepare_splice_transfer.py --discover`. Both earlier splice witness files stay unchanged. The starting family incorporates data adapted from Qiyuan Ma's published certificates (see the [previous proof](BINARY_CAPS.md) and [source and license notices](sources/README.txt)).
