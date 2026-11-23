# At least 21,158,736 three-color T boards

There are at least **21,158,736 distinct labeled boards**, in **1,763,228 distinct orbits** under color permutation and horizontal reflection. This adds **10,673,028 boards** to the previous lower bound of 10,485,708. The exact unrestricted count remains open. [Combined Lean theorem](SpliceFurtherCertificates.lean) · [Previous certificate](BINARY_CAPS.md)

| Family | Groups | Orbit representatives | Labeled boards |
|---|---:|---:|---:|
| Previous certificate | 28 | 873,809 | 10,485,708 |
| New groups with asymmetric pivots | 28 | 747,740 | 8,972,880 |
| New groups with palindromic pivots | 69 | 130,272 | 1,563,264 |
| Groups reusing earlier tails | 185 | 11,407 | 136,884 |
| **Total** | **310** | **1,763,228** | **21,158,736** |

## How the count is obtained

A board has ten centered rows of lengths 1, 3, …, 19. In each ordered T pattern, read the top cell and then the three cells underneath from left to right. There are 81 placements and 81 possible ordered quadruples. A valid board uses each quadruple once.

Fix the eleven cells of row 5, called the pivot. The five rows above it form a cap. With the pivot they realize 25 patterns. The four rows below form a tail. With the pivot they realize the complementary 56. A group records caps and tails with those fixed pattern sets, so every cap works with every tail. For example, changing just one digit from pivot `22220110022` to `22221110022` preserves the same six compatible caps. The two groups supply 25,209 and 25,117 tails, respectively. Together they give 12 × 6 × (25,209 + 25,117) = **3,623,472 labeled boards**. A completed board determines its pivot, its upper pattern set, and each of its constituent rows. [Splice proof](Splice.lean) · [Explicit new groups](splice_further.json)

### Counting reflections at a palindromic pivot

The new explicit families include 3 palindromic pivots. Reflection preserves each of these rows. The earlier apex-and-pivot test gives the same marker in both orientations here. The new proof reads all six upper rows for every group. A finite table identifies the symmetry that produced each transformed prefix. Lean checks this identification for all twelve operations on every recorded cap. Equal output boards must therefore come from the same operation, which can be inverted. [Prefix symmetry proof](SplicePrefixSymmetry.lean) · [Verified classifier](SplicePrefixData.lean)

For instance, one upper pattern set at pivot `22002020022` is invariant under reflection. We take one cap from each reflected pair and include the reflected tails in the tail set. Of 5,000 discovered tails, 2,318 also occur in the reflected list. Taking the union gives 2 cap representatives and 7,682 distinct tails, or 184,368 labeled boards. The deterministic sample at `22012221022` contributes another 198,984 boards from 62 binary-cap pattern sets. Its count uses 12,235 explicit tails. [Search replay](reproduce_symmetric.py)

### Reusing tails under a different pivot

Changing a pivot affects the T placements that touch row 5. The remaining lower rows can be reused whenever the new upper and lower pattern sets still partition the 81 quadruples. In one transfer, 299 tails from pivot `22111212222` also fit 4 caps at pivot `22111212221`, supplying 14,352 additional labeled boards. Each transfer names the earlier group and records which entries to take from its sorted tail list. Lean verifies the resulting group, and the combined theorem checks that every group has a distinct pivot and upper pattern set. [Transfer descriptors](splice_transfer.json) · [Transfer proof](SpliceTransfer.lean)

## Checking the result

From the project directory, the following commands check the four-layer theorem and independently expand the full certificate. The Python program enumerates T placements from Cartesian coordinates, checks all 81 patterns on each labeled board, and compares exact base-three board encodings for duplicates. The expanded audit passed on all 21,158,736 images and confirmed that the original 17,160 boards occur in the family. It compared complete encodings within each pivot orbit. The build log records the axioms reported by Lean. [Independent checker](verify_splice.py) · [Expanded audit result](splice-further-audit.log) · [Lean build log](splice-further-lean-build.log)

```sh
lake build SpliceFurtherCertificates
python verify_splice.py --through-transfer --expand --jobs 3
```

Regenerating the 286 new Lean source files from the four JSON witnesses reproduced them byte for byte. The discovery replay accepts one-based group numbers in `splice_further.json`. Group 18 checks the reflected-tail union in the example above, and group 27 checks one of the sampled binary-cap families. Searches used a mixture of exhaustive prefixes, fixed limits and specified samples. The theorem only uses the recorded witnesses.

```sh
python prepare_splice_extension.py --further
python reproduce_splice.py --certificate splice_further.json 18 27
```

The reverse search also reproduces the transfer descriptors exactly. Run `python prepare_splice_transfer.py --discover` to regenerate them. The two earlier splice witness files are included unchanged. The initial family incorporates data adapted from Qiyuan Ma’s published certificates. [Previous proof](BINARY_CAPS.md) · [Source and license notices](sources/README.txt)
