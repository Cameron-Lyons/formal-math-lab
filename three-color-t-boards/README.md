# Three-color prismatic T-tetromino ziggurats — Lean 4 proofs and counts

These are ternary de Bruijn polyomino colorings: `(T,3)`-prismatic colorings
of the ziggurat `Z_9`, with 100 cells and 81 ordered T patterns. Qiyuan Ma
already proved existence of a 60-board family. The results below strengthen
that lower bound; they do not give the unrestricted exact total.

**At least 45,083,592 distinct valid labeled boards exist**, in 3,756,966 disjoint orbits under color permutation and horizontal reflection. This adds 12,927,912 boards to the earlier certificate. The new proof includes boards whose first six rows are each mirror-symmetric. [Proof and counts](SPLICE_PALINDROMES.md) · [Lean theorem](SplicePalCertificates.lean) · [Download the proof and checkers](tboards-45083592-proof.zip)

```sh
lake build SplicePalCertificates
python verify_splice.py --all --native --jobs 4
```

Earlier lower bounds and their proofs are available. [32,155,680 boards](SPLICE_RANGES.md) · [21,158,736 boards](SPLICE_FURTHER.md) · [10,485,708 boards](BINARY_CAPS.md) · [348,960 boards](SPLICE_PROOF.md)

The [exact-count investigation](EXACT_COUNT.md) proves a global symmetry
reduction in Lean and supplies tested exhaustive counting models. The
unrestricted ternary total is still undetermined.

## The six-board proof

[Read the complete simple proof](PROOF.md) that **there are more than 60**
valid labeled boards. Six explicit boards share their first seven rows;
the proof verifies their patterns and shows that color permutations and
reflection give **72 distinct boards**. All data and the full finite check
are printed in the proof, with no dependence on a search or on a previously
established 60-board family.

It also identifies **board A outside all five published families** and proves
this directly by comparing just three rows. Lean checks A against all 60
published boards; the combined theorem is `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

The two optional checks of this small proof are:

```sh
python simple_proof.py --published
lake build SimpleProof
```

`SimpleProof.lean` proves `TBoards.Simple.at_least_72` and
`TBoards.Simple.more_than_60`. It imports none of the large `Extended` batches.
The Python checker also enumerates geometric T placements independently.

The small proof was rebuilt from scratch in an isolated directory on
22 November 2026; all 12 build jobs passed. Its
[build log](simple-lean-build.log) records source checksums and confirms
that the result uses only Lean's standard logical axioms.

## Prior-art status

The [dated literature check](PRIOR_ART.md) found no earlier published proof
of “more than 60” in the sources searched on **22 November 2026**. It checked
Ma's only public Zenodo version, the cited foundational papers and their
latest listed versions, and related search terminology. This does not
prove that no earlier proof exists. Board A's exclusion from the supplied
60-board family is certified; absolute historical priority is unconfirmed.
An open exact-count question alone would not establish novelty of this
strict lower bound.

## Earlier 17,160-board lower bound

The enlarged certificate supplies **17,160 distinct labeled boards**, belonging
to **1,430 disjoint color-permutation/reflection families**. Every board has ten
centered rows of lengths 1,3,...,19, and each ordered T color pattern occurs
exactly once. This is a lower bound; the unrestricted exact count is not determined.

## Lean verification of the earlier family

With elan installed, run from this directory:

```sh
lake build
```

The pinned version is Lean 4.36.0, using only its standard library. The earlier
result is `TBoards.at_least_17160` in `ExtendedCertificates.lean`:

```lean
∃ f : Fin 17160 → Board,
  (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j)
```

The proof uses kernel-checked `decide +kernel`, with no `sorry`, `native_decide`,
solver-correctness axiom, or assumption that the searches are exhaustive.
The build prints the theorem's axioms; its output is in `extended-lean-build.log`.
The archived build of the earlier family, including `SimpleProof`, passed all 117 jobs. The final theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`, Lean's standard logical axioms.
The earlier `at_least_72` and explicit first-witness novelty proof are retained
in `Certificates.lean`.

The proof has four parts:

1. `TBoards.lean` defines the exact geometry and original validity predicate.
   It proves there are 81 distinct placements and that each color quadruple
   has a unique placement on a valid board. All row lengths, palette bounds,
   and cell indices are checked.
2. `EfficientCheck.lean` proves that sorting the 81 base-three pattern codes
   and obtaining exactly 0,...,80 implies the original validity predicate.
   Each of the 1,430 representatives and its reflection receives this check
   in `Extended/Batch*.lean`.
3. `ColorSymmetry.lean` proves that global color permutations preserve validity.
   `CertifiedFamily.lean` attaches those validity proofs to each of the 17,160
   board values.
4. `Extended/Blocks.lean` checks every board's numeric fingerprint. The entire
   sequence is then proved strictly increasing. `SortedFamily.lean` proves
   this implies distinct boards, and the final theorem constructs the
   injective indexed family above.

The numeric fingerprint is the flattened 100-digit base-three integer. The
proof of distinctness uses the checked inequalities between fingerprints;
no assumption about a hashing algorithm is involved. Compilation is split
into small certificates, with at most four orientation batches building at once.

## Data and independent audit

```sh
python collect_extended.py
```

This independently checks every one of the 17,160 boards using Cartesian
coordinates. It regenerates the representative/provenance table, the full
sorted family, and the audit summary. To regenerate the corresponding Lean
source and verify it:

```sh
python prepare_extended.py
lake build
```

The generator is outside Lean's trusted computing base: all generated board
data, fingerprints, validity proofs, distinctness, and the cardinality bound
are subsequently checked by Lean.

- `extended_seeds.json`: 1,430 representatives with source provenance.
- `extended_family.json`: all 17,160 boards, sorted by their numeric encodings.
- `extended_summary.json`: audit counts, checksums, and search scope.
- `extended_prefix0.jsonl`: 136 further representatives from the first prefix.
- `more_results.jsonl`: 1,288 further representatives from the second prefix.
- `prefix_result.json`: the first new representative, which raised the bound to 72.
- `novel_patterns.csv`: the 81 pattern locations for that first new board.
- `sources/`: the unchanged published preprint, certificates, programs, and licenses.

Each JSON row is a string with `0 = red`, `1 = green`, `2 = blue`.

## Search and scope

The two extended searches fixed rows 0 through 5 of the first and second
published representatives and enumerated the remaining cells. They reject
repeated patterns and enforce the necessary condition that every color occurs
27 times in each of the four T positions. Canonicalization removes global
color permutations and horizontal reflection.

The first fixed-prefix search exhausted its region: 138 completions, including
the published representative and our first new representative, hence 136
additional families. It visited 10,744,033,875 nodes in approximately 117 seconds.
Its completeness is a result of the C++ enumeration and is **not Lean-proved**.

The second search found 1,290 completions, including two published ones, before
its 180-second deadline. Its 1,288 additional families are supplied as explicit
certificates. That search was not exhaustive. The overall count is
`(5 + 1 + 136 + 1288) * 12 = 17160`.

The optional discovery rerun requires `g++`:

```sh
python reproduce_extended_search.py --seconds 300
```

The rerun finishes the first prefix and stops the second after reproducing its
recorded 1,288 new families. It compares the ordered representative lists with
the supplied data. A time limit is per search and depends on the machine; a
timeout proves nothing about nonexistence. `--smoke` provides a short check of
the discovery executable and wrapper. Discovery is unnecessary to verify the
Lean proof or the saved certificates.

The replay wrapper's smoke test passed. The original searches and full
coordinate audit completed as recorded; the optional full discovery replay
was not repeated after adding its deterministic count limit.

## Source and attribution

The original five seeds and downloaded files in `sources/` come from Qiyuan
Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes*, version 1.0,
25 October 2026, [DOI 10.5281/zenodo.23631079](https://doi.org/10.5281/zenodo.23631079).
The downloaded archive's MD5 matches the published value
`75f7fc208678c82d0269fa453942a80b`; all its internal SHA-256 checksums passed.

The source manuscript and certificate data are CC-BY-4.0; the source Python
programs are MIT licensed. Original notices and full licenses are preserved
under `sources/`. The first five representatives and their symmetry images are adapted from that
certificate data. All additional representatives were discovered in this
workspace. Their provenance is recorded in `extended_seeds.json`. The new C++
discovery programs and Lean formalization were written for this task.
