# Three-color prismatic T-tetromino ziggurats

A `(T, 3)`-prismatic coloring of the 100-cell ziggurat $Z_9$ (10 centered rows of lengths $1, 3, \ldots, 19$) is a 3-coloring where each of the $3^4 = 81$ ordered 3-color T-tetromino patterns appears once. Qiyuan Ma (`10.5281/zenodo.23631079`, v1.0, 25 October 2026) proved that valid boards exist and gave 60 labeled boards (5 orbits of 12). The exact total number of valid boards is still open.

The Lean 4 proofs in this folder prove larger lower bounds and a global symmetry theorem:

* At least 45,083,592 distinct valid labeled boards (3,756,966 disjoint orbits of size 12 under the 6 color permutations and horizontal reflection), verified in `TBoards.at_least_45083592` ([SplicePalCertificates.lean](SplicePalCertificates.lean)).
* A small standalone proof of more than 60 boards (72 distinct boards, plus a direct proof that board A is outside all 60 published boards: `TBoards.Simple.problem_solved` in [SimpleProof.lean](SimpleProof.lean)).
* Global symmetry theorem: every valid ternary T-board, not just the ones in our certificates, has a trivial stabilizer and therefore 12 distinct images under color permutations and horizontal reflection (`TBoards.ExactSymmetry.stabilizer_trivial` in [ExactSymmetry.lean](ExactSymmetry.lean) and `TBoards.ExactOrbit.twelve_distinct_images` in [ExactOrbit.lean](ExactOrbit.lean)).

| Field | Summary |
| --- | --- |
| Problem | `(T, 3)`-prismatic coloring of the 100-cell ziggurat $Z_9$ (81 ordered T patterns), ternary de Bruijn polyominoes, Qiyuan Ma (`10.5281/zenodo.23631079`) |
| Status | Lower bound $\ge 45{,}083{,}592$ labeled boards and global orbit-size-12 theorem proved in Lean 4. Exact total is still open. |
| Main theorems | `TBoards.at_least_45083592` ([SplicePalCertificates.lean](SplicePalCertificates.lean)); `TBoards.Simple.problem_solved`, `at_least_72`, `more_than_60` ([SimpleProof.lean](SimpleProof.lean)); `TBoards.ExactSymmetry.stabilizer_trivial` ([ExactSymmetry.lean](ExactSymmetry.lean)); `TBoards.ExactOrbit.twelve_distinct_images` ([ExactOrbit.lean](ExactOrbit.lean)) |
| Verification | `lake build SimpleProof` (small proof); `lake build ExactSymmetry ExactOrbit` (global symmetry); `lake build SplicePalCertificates` (45,083,592 lower bound); Lean 4.36.0, stdlib only (kernel-checked) |
| Prior art | Checked 22 November 2026: Qiyuan Ma v1.0 proved existence with 60 boards; no earlier proof of $> 60$ or $\ge 45{,}083{,}592$ boards was found (bounded search, not a claim of absolute priority). See [PRIOR_ART.md](PRIOR_ART.md) and the [collection audit](../PRIOR_ART.md#three-color-prismatic-t-tetromino-boards). |

## Main lower bound: at least 45,083,592 boards

There are at least 45,083,592 distinct valid labeled boards, forming 3,756,966 disjoint orbits under color permutation and horizontal reflection. This adds 12,927,912 boards to the earlier 32,155,680-board certificate by including boards whose first six rows are each mirror-symmetric ([SPLICE_PALINDROMES.md](SPLICE_PALINDROMES.md), [SplicePalCertificates.lean](SplicePalCertificates.lean)).

```sh
lake build SplicePalCertificates
python verify_splice.py --all --native --jobs 4
```

Earlier certified lower bounds and write-ups are still here: [32,155,680 boards](SPLICE_RANGES.md), [21,158,736 boards](SPLICE_FURTHER.md), [10,485,708 boards](BINARY_CAPS.md), and [348,960 boards](SPLICE_PROOF.md).

The [exact-count investigation](EXACT_COUNT.md) covers the kernel-checked global orbit-size-12 proof (`lake build ExactSymmetry ExactOrbit`) and all exhaustive counting models we tested. The unrestricted ternary total is still unknown.

## The six-board standalone proof (> 60 boards)

[PROOF.md](PROOF.md) gives a short, self-contained proof that there are more than 60 valid labeled boards. Six explicit boards share their first seven rows; the proof checks their patterns and shows that color permutations and reflection produce 72 distinct boards. All data and finite checks appear right in the proof, with no dependence on a search program or on Ma's 60-board family.

It also shows that board A falls outside all five published families by comparing three rows. Lean checks board A against all 60 published boards, giving the combined theorem `TBoards.Simple.problem_solved`:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

You can check this small proof on its own:

```sh
python simple_proof.py --published
lake build SimpleProof
```

`SimpleProof.lean` proves `TBoards.Simple.at_least_72` and `TBoards.Simple.more_than_60` without importing any of the large `Extended` batches. The Python checker enumerates geometric T placements independently. A clean rebuild in an isolated directory passed on 22 November 2026 (all 12 build jobs passed; [simple-lean-build.log](simple-lean-build.log) records source checksums and confirms that only Lean's standard logical axioms are used).

## Prior-art status

The [dated literature check](PRIOR_ART.md) found no earlier published proof of "more than 60" in the sources searched on 22 November 2026. It checked Ma's only public Zenodo version, the two cited foundational papers (*De Bruijn Polyominoes* `arXiv:2405.18543v2` and *Polyomino Density* `arXiv:2608.29231v1`), and related search terms. We certified that board A is outside the 60 published boards, while absolute historical priority remains unconfirmed.

## Earlier 17,160-board lower bound

The earlier enlarged certificate gives 17,160 distinct labeled boards in 1,430 disjoint color-permutation/reflection families (`TBoards.at_least_17160` in [ExtendedCertificates.lean](ExtendedCertificates.lean)):

```lean
∃ f : Fin 17160 → Board,
  (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j)
```

With `elan` installed (pinned Lean 4.36.0, stdlib only), run `lake build` from this directory. The proof uses kernel-checked `decide +kernel`, with no `sorry`, `native_decide`, solver-correctness axiom, or exhaustiveness assumption (`extended-lean-build.log` confirms only `propext`, `Classical.choice`, and `Quot.sound`). The earlier `at_least_72` and first-witness novelty proofs stay in [Certificates.lean](Certificates.lean).

The proof has four parts:

1. [TBoards.lean](TBoards.lean) defines the geometry and validity predicate, proving there are 81 distinct placements and each color quadruple occurs once on a valid board.
2. [EfficientCheck.lean](EfficientCheck.lean) proves that if sorting the 81 base-3 pattern codes produces `0, ..., 80`, the board is valid. Each of the 1,430 representatives and its reflection is checked in `Extended/Batch*.lean`.
3. [ColorSymmetry.lean](ColorSymmetry.lean) proves global color permutations preserve validity, and [CertifiedFamily.lean](CertifiedFamily.lean) attaches validity proofs to all 17,160 boards.
4. `Extended/Blocks.lean` and [SortedFamily.lean](SortedFamily.lean) check each board's 100-digit base-3 number and prove the list is strictly increasing, certifying distinctness without hashing assumptions.

## Data and independent audit

```sh
python collect_extended.py
```

This script independently checks all 17,160 boards in Cartesian coordinates and rebuilds the provenance table, sorted family, and audit summary. To regenerate the Lean files and rebuild them:

```sh
python prepare_extended.py
lake build
```

The generator sits outside Lean's trusted computing base; Lean checks all generated board data, encodings, validity proofs, distinctness, and counts. Key data files are `extended_seeds.json` (1,430 representatives with provenance), `extended_family.json` (17,160 sorted boards), `extended_summary.json`, `extended_prefix0.jsonl` (136 families from prefix 1), `more_results.jsonl` (1,288 families from prefix 2), `prefix_result.json`, `novel_patterns.csv`, and `sources/` (unchanged published files). Each JSON row uses `0 = red`, `1 = green`, `2 = blue`.

## Search and scope

The two earlier extended searches fixed rows 0-5 of the first and second published representatives:

* The first fixed-prefix search exhausted its region (138 completions: the published representative, the first new representative, and 136 more families; 10,744,033,875 nodes in ~117 s; completeness comes from the C++ search, not Lean).
* The second search found 1,290 completions (including 2 published ones) in 180 s, giving 1,288 more certified families (not exhaustive). Together: `(5 + 1 + 136 + 1288) * 12 = 17,160`.

Optional discovery replay (`g++` required; not needed to verify the Lean proofs or saved certificates):

```sh
python reproduce_extended_search.py --seconds 300
```

## Source and attribution

The original five seeds and downloaded files in `sources/` come from Qiyuan Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes*, version 1.0, 25 October 2026, [DOI 10.5281/zenodo.23631079](https://doi.org/10.5281/zenodo.23631079). The downloaded archive's MD5 matches `75f7fc208678c82d0269fa453942a80b`, and all internal SHA-256 checksums passed.

The source manuscript and certificate data are CC-BY-4.0; the source Python programs are MIT licensed. Original notices and full licenses are kept under [sources/LICENSE_SCOPE.txt](sources/LICENSE_SCOPE.txt). The first five representatives and their symmetry images come from that certificate data; all other representatives were found here (provenance is recorded in `extended_seeds.json`).
