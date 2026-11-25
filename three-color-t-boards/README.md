# Three-color prismatic T-tetromino ziggurats ((T, 3)-prismatic Z_9): at least 45,083,592 boards and global orbit size 12 — Lean 4 proofs

This Lean 4 project studies **ternary de Bruijn polyomino colorings** — specifically **`(T, 3)`-prismatic colorings of the 100-cell ziggurat $Z_9$** (10 centered rows of lengths $1, 3, \ldots, 19$, where every one of the $3^4 = 81$ ordered 3-color T-tetromino patterns occurs **exactly once**). Qiyuan Ma (`10.5281/zenodo.23631079`, v1.0, 25 October 2026) proved existence and supplied 60 labeled boards (5 orbits of 12).

This project proves **much stronger Lean-certified lower bounds** and a **global symmetry theorem**:

* **At least 45,083,592 distinct valid labeled boards** (3,756,966 disjoint orbits of size 12 under the 6 color permutations and horizontal reflection), verified in Lean (`TBoards.at_least_45083592` in [SplicePalCertificates.lean](SplicePalCertificates.lean)).
* **Small standalone proof of more than 60 boards** (72 distinct boards, plus a direct proof that board A lies outside all 60 published boards: `TBoards.Simple.problem_solved` in [SimpleProof.lean](SimpleProof.lean)).
* **Global symmetry theorem:** **every** valid ternary T-board (not only those in the certificates) has trivial stabilizer and therefore exactly **12 distinct images** under color permutations and horizontal reflection (`TBoards.ExactSymmetry.stabilizer_trivial` in [ExactSymmetry.lean](ExactSymmetry.lean), `TBoards.ExactOrbit.twelve_distinct_images` in [ExactOrbit.lean](ExactOrbit.lean)).

**Status:** these are Lean-certified lower bounds and global structural theorems; **the exact unrestricted total count of valid boards remains open.**

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Three-color prismatic T-tetromino ziggurat**, `(T, 3)`-prismatic coloring of `Z_9` (100 cells, 81 ordered T patterns), ternary de Bruijn polyominoes, Qiyuan Ma (`10.5281/zenodo.23631079`) |
| **Status** | **Lower bound $\ge 45{,}083{,}592$ labeled boards and global orbit-size-12 theorem proved in Lean 4.** Exact unrestricted total remains open. |
| **Main Lean theorems** | `TBoards.at_least_45083592` ([SplicePalCertificates.lean](SplicePalCertificates.lean)); `TBoards.Simple.problem_solved`, `at_least_72`, `more_than_60` ([SimpleProof.lean](SimpleProof.lean)); `TBoards.ExactSymmetry.stabilizer_trivial` ([ExactSymmetry.lean](ExactSymmetry.lean)); `TBoards.ExactOrbit.twelve_distinct_images` ([ExactOrbit.lean](ExactOrbit.lean)) |
| **Verification** | `lake build SimpleProof` (fast small proof); `lake build ExactSymmetry ExactOrbit` (global symmetry); `lake build SplicePalCertificates` (45,083,592 lower bound); Lean 4.36.0, stdlib only (kernel-checked) |
| **Prior-art status** | Checked **22 November 2026**: Qiyuan Ma v1.0 proved existence with 60 boards; no earlier proof of $> 60$ or $\ge 45{,}083{,}592$ boards located (bounded search, not a claim of absolute priority). See [PRIOR_ART.md](PRIOR_ART.md) and [collection audit](../PRIOR_ART.md#three-color-prismatic-t-tetromino-boards). |

## Main lower bound: at least 45,083,592 boards

**At least 45,083,592 distinct valid labeled boards exist**, in 3,756,966 disjoint orbits under color permutation and horizontal reflection. This adds 12,927,912 boards to the earlier 32,155,680-board certificate by including boards whose first six rows are each mirror-symmetric. [Proof and counts](SPLICE_PALINDROMES.md) · [Lean theorem](SplicePalCertificates.lean) · [Download the proof and checkers](tboards-45083592-proof.zip)

```sh
lake build SplicePalCertificates
python verify_splice.py --all --native --jobs 4
```

Earlier certified lower bounds and their write-ups remain available: [32,155,680 boards](SPLICE_RANGES.md) · [21,158,736 boards](SPLICE_FURTHER.md) · [10,485,708 boards](BINARY_CAPS.md) · [348,960 boards](SPLICE_PROOF.md).

The [exact-count investigation](EXACT_COUNT.md) documents the kernel-checked global orbit-size-12 proof (`lake build ExactSymmetry ExactOrbit`) and tested exhaustive counting models. The unrestricted ternary total is still undetermined.

## The six-board standalone proof (> 60 boards)

[Read the complete simple proof](PROOF.md) that **there are more than 60** valid labeled boards. Six explicit boards share their first seven rows; the proof verifies their patterns and shows that color permutations and reflection give **72 distinct boards**. All data and the full finite check are printed in the proof, with no dependence on a search or on a previously established 60-board family.

It also identifies **board A outside all five published families** and proves this directly by comparing just three rows. Lean checks A against all 60 published boards; the combined theorem is `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

Check this small proof independently:

```sh
python simple_proof.py --published
lake build SimpleProof
```

`SimpleProof.lean` proves `TBoards.Simple.at_least_72` and `TBoards.Simple.more_than_60` without importing any of the large `Extended` batches. The Python checker also enumerates geometric T placements independently. Rebuilt from scratch in an isolated directory on 22 November 2026 (all 12 build jobs passed; [build log](simple-lean-build.log) records source checksums and confirms only Lean's standard logical axioms).

## Prior-art status

The [dated literature check](PRIOR_ART.md) found no earlier published proof of "more than 60" in the sources searched on **22 November 2026**. It checked Ma's only public Zenodo version, the cited foundational papers (*De Bruijn Polyominoes* `arXiv:2405.18543v2` and *Polyomino Density* `arXiv:2608.29231v1`), and related search terminology. This does not prove that no earlier proof exists. Board A's exclusion from the supplied 60-board family is certified; absolute historical priority is unconfirmed.

## Earlier 17,160-board lower bound

The earlier enlarged certificate supplies **17,160 distinct labeled boards**, belonging to **1,430 disjoint color-permutation/reflection families** (`TBoards.at_least_17160` in [ExtendedCertificates.lean](ExtendedCertificates.lean)):

```lean
∃ f : Fin 17160 → Board,
  (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j)
```

With `elan` installed (pinned Lean **4.36.0**, standard library only), run `lake build` from this directory. The proof uses kernel-checked `decide +kernel`, with no `sorry`, `native_decide`, solver-correctness axiom, or assumption that searches are exhaustive (`extended-lean-build.log` confirms only `propext`, `Classical.choice`, and `Quot.sound`). The earlier `at_least_72` and first-witness novelty proof are retained in [Certificates.lean](Certificates.lean).

The architecture has four parts:

1. [TBoards.lean](TBoards.lean) defines the exact geometry and original validity predicate, proving there are 81 distinct placements and each color quadruple occurs uniquely on a valid board.
2. [EfficientCheck.lean](EfficientCheck.lean) proves that sorting the 81 base-3 pattern codes and obtaining `0, ..., 80` implies validity; each of the 1,430 representatives and its reflection is checked in `Extended/Batch*.lean`.
3. [ColorSymmetry.lean](ColorSymmetry.lean) proves global color permutations preserve validity, and [CertifiedFamily.lean](CertifiedFamily.lean) attaches validity proofs to all 17,160 boards.
4. `Extended/Blocks.lean` and [SortedFamily.lean](SortedFamily.lean) check each board's 100-digit base-3 numeric encoding and prove the sequence is strictly increasing, certifying distinctness without any hashing assumption.

## Data and independent audit

```sh
python collect_extended.py
```

This independently checks all 17,160 boards using Cartesian coordinates and regenerates the provenance table, sorted family, and audit summary. To regenerate the corresponding Lean source and rebuild it:

```sh
python prepare_extended.py
lake build
```

The generator sits outside Lean's trusted computing base; Lean checks all generated board data, encodings, validity proofs, distinctness, and cardinality. Key data files include `extended_seeds.json` (1,430 representatives with provenance), `extended_family.json` (17,160 sorted boards), `extended_summary.json`, `extended_prefix0.jsonl` (136 families from prefix 1), `more_results.jsonl` (1,288 families from prefix 2), `prefix_result.json`, `novel_patterns.csv`, and `sources/` (unchanged published files). Each JSON row uses `0 = red`, `1 = green`, `2 = blue`.

## Search and scope

The two earlier extended searches fixed rows 0–5 of the first and second published representatives:

* The first fixed-prefix search exhausted its region (138 completions: the published representative, the first new representative, and 136 more families; 10,744,033,875 nodes in ~117 s; completeness is from the C++ enumeration, not Lean-proved).
* The second search found 1,290 completions (including 2 published ones) within 180 s, yielding 1,288 additional certified families (not exhaustive). Together: `(5 + 1 + 136 + 1288) * 12 = 17,160`.

Optional discovery replay (`g++` required; unnecessary to verify the Lean proofs or saved certificates):

```sh
python reproduce_extended_search.py --seconds 300
```

## Source and attribution

The original five seeds and downloaded files in `sources/` come from Qiyuan Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes*, version 1.0, 25 October 2026, [DOI 10.5281/zenodo.23631079](https://doi.org/10.5281/zenodo.23631079). The downloaded archive's MD5 matches `75f7fc208678c82d0269fa453942a80b`, and all internal SHA-256 checksums passed.

The source manuscript and certificate data are CC-BY-4.0; the source Python programs are MIT licensed. Original notices and full licenses are preserved under [sources/LICENSE_SCOPE.txt](sources/LICENSE_SCOPE.txt). The first five representatives and their symmetry images are adapted from that certificate data; all additional representatives were discovered in this workspace (provenance recorded in `extended_seeds.json`). The new C++ discovery programs and Lean formalization were written for this task.
