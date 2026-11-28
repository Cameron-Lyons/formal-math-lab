# Three-color prismatic T-tetromino ziggurats

Picture a 10-row triangular pyramid of 100 unit squares — the **ziggurat** $Z_9$ — whose centered rows have lengths $1, 3, 5, 7, 9, 11, 13, 15, 17, 19$. Color every square red (`0`), green (`1`), or blue (`2`), and look at every upright **T-tetromino** (one cell directly above the middle of three consecutive cells in the next row):

```text
      t
    l m r
```

Only translates of this single upright orientation count. Inside $Z_9$, there are $1 + 3 + 5 + \cdots + 17 = 81$ such T placements, and there are $3^4 = 81$ possible ordered 3-color T patterns. A coloring is **`(T, 3)`-prismatic** (a valid three-color T board, or ternary de Bruijn polyomino) if every one of those 81 patterns appears **exactly once**.

Qiyuan Ma (`10.5281/zenodo.23631079`, v1.0, 25 October 2026) proved that valid boards exist and exhibited **60 labeled boards** (5 symmetry orbits of 12). The exact total number of valid boards remains an open problem.

The Lean 4 proofs in this folder establish dramatically larger lower bounds together with a global symmetry theorem:

* **At least 45,083,592 distinct valid labeled boards** (3,756,966 disjoint orbits of size 12 under the 6 color permutations and horizontal reflection), verified in `TBoards.at_least_45083592` ([SplicePalCertificates.lean](SplicePalCertificates.lean)).
* **A small, human-checkable standalone proof of $> 60$ boards**: 72 distinct valid boards from six explicit witnesses, plus a direct proof that board A lies outside all 60 published boards (`TBoards.Simple.problem_solved` in [SimpleProof.lean](SimpleProof.lean)).
* **A global symmetry theorem**: *every* valid ternary T board — not merely the boards in our certificates — has a trivial stabilizer and therefore generates exactly 12 distinct valid images under color permutations and horizontal reflection (`TBoards.ExactSymmetry.stabilizer_trivial` in [ExactSymmetry.lean](ExactSymmetry.lean) and `TBoards.ExactOrbit.twelve_distinct_images` in [ExactOrbit.lean](ExactOrbit.lean)).

| Field | Summary |
| --- | --- |
| Problem | `(T, 3)`-prismatic coloring of the 100-cell ziggurat $Z_9$ (81 ordered T patterns), ternary de Bruijn polyominoes, Qiyuan Ma (`10.5281/zenodo.23631079`) |
| Status | Lower bound $\ge 45{,}083{,}592$ labeled boards and global orbit-size-12 theorem proved in Lean 4. Exact total is still open. |
| Main theorems | `TBoards.at_least_45083592` ([SplicePalCertificates.lean](SplicePalCertificates.lean)); `TBoards.Simple.problem_solved`, `at_least_72`, `more_than_60` ([SimpleProof.lean](SimpleProof.lean)); `TBoards.ExactSymmetry.stabilizer_trivial` ([ExactSymmetry.lean](ExactSymmetry.lean)); `TBoards.ExactOrbit.twelve_distinct_images` ([ExactOrbit.lean](ExactOrbit.lean)) |
| Verification | `lake build SimpleProof` (small proof); `lake build ExactSymmetry ExactOrbit` (global symmetry); `lake build SplicePalCertificates` (45,083,592 lower bound); Lean 4.36.0, stdlib only (kernel-checked) |
| Prior art | Checked 22 November 2026: Qiyuan Ma v1.0 proved existence with 60 boards; no earlier proof of $> 60$ or $\ge 45{,}083{,}592$ boards was found (bounded search, not a claim of absolute priority). |

## The big ideas

Two structural ideas drive all the results in this folder.

**1. Why every valid board sits in an orbit of size 12.**
You can transform any valid board in two ways that preserve validity: permute the three colors globally ($3! = 6$ ways) or reflect every row left-to-right ($2$ orientations). Together these form a 12-element symmetry group. Could a valid board ever map to itself under a nontrivial move? No — because a valid board puts the 81 T placements in one-to-one correspondence with the 81 color patterns, so any symmetry fixing the board would have to fix the same number of placements and patterns:

* An unreflected color permutation leaves all **81** placements fixed, but only the identity fixes all 81 patterns (a color swap fixes 1 pattern; a 3-cycle fixes 0).
* A horizontal reflection (possibly combined with a color permutation) fixes the **9** center-column placements, whereas on patterns it fixes **27, 3, or 0** patterns — never 9.

Thus the stabilizer is always trivial, and every valid board produces 12 distinct labeled boards.

**2. How splicing multiplies the lower bound.**
Fixing row 5 (11 cells, called the **pivot**) splits the remaining nine rows into a 5-row **cap** above (covering 25 T patterns with the pivot) and a 4-row **tail** below (covering the remaining 56 T patterns). Whenever $C$ different caps all induce the *exact same* 25 patterns with the pivot, and $T$ tails all induce the complementary 56 patterns, **every cap pairs validly with every tail**. That turns additive searches into a $C \times T$ product — and applying the 12 symmetries multiplies it again. Pushing this construction through binary caps, palindromic pivots, tail transfers, lexicographic continuations, and fully palindromic prefixes grows the certified lower bound step by step to **45,083,592** labeled boards (3,756,966 disjoint orbits of size 12).

## Main lower bound: at least 45,083,592 boards

There are at least **45,083,592** distinct valid labeled boards, forming **3,756,966** disjoint orbits under color permutation and horizontal reflection ([SplicePalCertificates.lean](SplicePalCertificates.lean)).

```sh
lake build SplicePalCertificates
```

The [exact-count theorems](EXACT_COUNT.md) document the kernel-checked global orbit-size-12 proof (`lake build ExactSymmetry ExactOrbit`), reduced marginal characterization and counterexample (`ExactMarginals`, `MarginalCounterexample`), modular/parity saturation (`ExactParity`), and $\mathbb{F}_3$ moment equivalence (`ExactNativeMoments`). The unrestricted ternary total is still unknown.

## The six-board standalone proof (> 60 boards)

[SimpleProof.lean](SimpleProof.lean) gives a short, completely self-contained kernel proof (`TBoards.Simple.at_least_72`, `TBoards.Simple.more_than_60`, and `TBoards.Simple.problem_solved`) that six explicit boards generate 72 distinct valid labeled boards and that board A lies outside all 60 published boards:

```lean
MoreThanSixty ∧ Valid board0 ∧ board0 ∉ TBoards.published
```

To verify this small proof on its own:

```sh
lake build SimpleProof
```

## Source and attribution

The original five published representatives reused in [BoardData.lean](BoardData.lean) come from Qiyuan Ma, *Explicit Three- and Four-Color Prismatic T-Tetrominoes*, version 1.0, 25 October 2026, [DOI 10.5281/zenodo.23631079](https://doi.org/10.5281/zenodo.23631079), licensed under CC-BY-4.0. Original attribution and license terms are kept under [sources/LICENSE_SCOPE.txt](sources/LICENSE_SCOPE.txt) and [sources/LICENSES/CC-BY-4.0.txt](sources/LICENSES/CC-BY-4.0.txt).
