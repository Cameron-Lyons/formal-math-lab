# Nine-bit snake-in-the-box ($Q_9$, length 191 / 192)

Picture the $2^9 = 512$ corners of the 9-dimensional hypercube $Q_9$, labeled by all 9-bit binary strings, where two corners are joined by an edge if they differ in exactly 1 bit (Hamming distance 1). A **snake-in-the-box** is a path of distinct vertices along edges of the hypercube that never comes back to touch itself—not even by passing adjacent to an earlier corner. Formally, it is an *induced path*: consecutive vertices differ in 1 bit, while any two non-consecutive vertices differ in at least 2 bits (no shortcuts or "chords").

> **Tiny example in $Q_3$:** The 4-step path `000 → 001 → 011 → 111 → 110` is a valid snake of length 4 (4 edges, 5 vertices): every consecutive pair differs in 1 bit, and every non-consecutive pair differs in 2 or 3 bits. Trying to extend it to `100` fails because `100` is only 1 bit away from the starting vertex `000`.

Two snakes are considered **equivalent** if one can be transformed into the other by reversing the path or applying a hypercube symmetry (permuting the 9 bit positions and flipping any fixed subset of bit positions across every vertex). Orland et al. (`arXiv:2607.15270`) published 131 inequivalent record snakes of length 191 in $Q_9$—none extendable by a single step—and asked two open questions: does a 192-step snake exist, and does any 132nd equivalence class of length 191 exist?

The Lean 4 proofs here formally verify all 131 published 191-step snakes and show that no new solution lies anywhere near their tails: keeping the first 156 steps of *any* published snake (read from either end) admits no 192-step completion (`Snake.bank_no_192`) and no new 191-step equivalence class (`Snake.bank_no_new_191`). We also prove a fast, kernel-checked endpoint test: any valid 191-step snake whose forward and backward 17-step Hamming-distance profiles agree is guaranteed to belong to a brand-new equivalence class (`Snake.outside_bank_of_end_profiles`). Both open questions remain unresolved.

| Field | Summary |
| --- | --- |
| Problem | Nine-bit snake-in-the-box ($Q_9$, length 191 vs. 192, 131 equivalence classes), Orland et al. (`arXiv:2607.15270v3`, §8; `Math-AI-Caltech/Snake-in-the-Box`), Kunt, Koch, and Park (`arXiv:2611.25268`) |
| Status | Partial results (156-step prefix closure and endpoint novelty test). Existence of a 192-step snake or a new 191-step class in $Q_9$ remains open. |
| Main theorems | `Snake.bank_no_192` ([Results.lean](Results.lean)), `Snake.bank_no_new_191`, `Snake.outside_bank_of_end_profiles` ([Closure.lean](Closure.lean)); kernel-checked 171-step exclusion and bank validity in [KernelChecks.lean](KernelChecks.lean) |
| Verification | `lake build` (Lean 4.36.0, stdlib only; 131-bank validity, 17-step endpoint test, and 171-step exclusion are kernel-checked; 156-step exhaustive closures and pairwise inequivalence use `native_decide`) |
| Prior art | Checked 24 November 2026: Orland et al. published the 131 classes of length 191 and noted no 1-step extension exists; Kunt, Koch, and Park also identify dimension 9 as the smallest open case. |

## Lean results

- **Prefix closure at step 156 (`Snake.bank_no_192`, `Snake.bank_no_new_191`):** Take any of the 131 published 191-step snakes, orient it from either end (giving $2 \times 131 = 262$ oriented prefixes), and freeze its first 156 steps. Exhaustively searching every legal continuation of single-bit flips proves:
  1. No 36-step continuation (reaching length 192) exists ([Results.lean](Results.lean)).
  2. Every 35-step continuation (reaching length 191) is equivalent to one of the 131 published snakes under path reversal, coordinate permutation, and coordinate bit-flips ([Closure.lean](Closure.lean)).
- **Pure kernel 171-step exclusion ([KernelChecks.lean](KernelChecks.lean)):** Without using `native_decide`, Lean's kernel directly verifies that all 131 published snakes are valid induced paths in $Q_9$ and proves that no 192-step continuation can keep the first 171 steps of any of them.
- **Endpoint novelty test for a new 191-step class (`Snake.outside_bank_of_end_profiles`, [EndProfiles.lean](EndProfiles.lean), [Closure.lean](Closure.lean)):** Starting from one endpoint of a snake, record the Hamming distance (number of differing bits) from that endpoint after steps $1, 2, \ldots, 17$; repeat starting from the opposite endpoint. Hypercube symmetries (bit permutations and XOR bit-flips) leave both lists unchanged, while reversing the snake simply swaps the two lists. Lean's kernel verifies that all 131 published snakes have *unequal* forward and backward 17-step profiles. Consequently, any valid 191-step snake in $Q_9$ whose two 17-step endpoint profiles match cannot be equivalent to any of the 131 known snakes.

## Verification and trust boundary

Run from this directory with Lean 4.36.0 (stdlib only):

```sh
lake build
```

- **Pure Lean kernel:** Validity of all 131 published snakes, the 17-step endpoint novelty test (`Snake.outside_bank_of_end_profiles`), and the 171-step no-192 exclusion ([KernelChecks.lean](KernelChecks.lean)).
- **`native_decide` (trusts Lean's compiler and runtime):** The 156-step exhaustive closures (`Snake.bank_no_192`, `Snake.bank_no_new_191`) and pairwise inequivalence of the 131 published snakes.

## References

- [Orland et al., `arXiv:2607.15270v3`, §8](https://arxiv.org/html/2607.15270v3#S8) and [pinned published data (`Math-AI-Caltech/Snake-in-the-Box`)](https://github.com/Math-AI-Caltech/Snake-in-the-Box/tree/46c765399353a588ea50444a5d6610f53102b1c2)
- [Kunt, Koch, and Park, `arXiv:2611.25268`](https://arxiv.org/abs/2611.25268)
- [Bank.lean](Bank.lean)
