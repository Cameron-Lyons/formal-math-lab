# Nine-bit snake-in-the-box (Q_9, length 191 / 192): 156-step prefix closure and endpoint novelty test — Lean 4 proofs

**Status: whether a 192-step snake or a 132nd inequivalent 191-step snake exists in the 9-dimensional hypercube $Q_9$ remains open.** A *snake-in-the-box* in $Q_9$ is an induced path of distinct 9-bit strings where consecutive vertices differ in 1 bit (Hamming distance 1) and all non-consecutive vertices differ in at least 2 bits (Hamming distance $\ge 2$). Orland et al. (`arXiv:2607.15270`) published 131 inequivalent record snakes of length **191** in $Q_9$ (none admitting a 1-step extension) and asked whether a 192-step snake or another 191-step equivalence class exists.

This Lean 4 project verifies all 131 published 191-step snakes and proves two structural results: keeping the first **156 steps** of any published snake (read from either end) admits **no 192-step completion** (`Snake.bank_no_192`) and **no new 191-step equivalence class** (`Snake.bank_no_new_191`); and any 191-step snake whose 17-step endpoint Hamming-distance profiles agree from both ends is guaranteed to belong to a **new equivalence class** (`Snake.outside_bank_of_end_profiles`).

| Field | Summary |
| --- | --- |
| **Problem & identifiers** | **Nine-bit snake-in-the-box** (`Q_9`, 9-dimensional hypercube induced path, length 191 vs. 192, 131 equivalence classes), Orland et al. (`arXiv:2607.15270v3`, §8; `Math-AI-Caltech/Snake-in-the-Box`), Kunt–Koch–Park (`arXiv:2611.25268`) |
| **Status** | **Partial results (156-step prefix closure and endpoint-symmetry novelty test).** Unrestricted existence of a 192-step snake or a new 191-step class in $Q_9$ remains open. |
| **Main Lean theorems** | `Snake.bank_no_192` ([Results.lean](Results.lean)), `Snake.bank_no_new_191`, `Snake.outside_bank_of_end_profiles` ([Closure.lean](Closure.lean)); kernel-checked 171-step exclusion and bank validity in [KernelChecks.lean](KernelChecks.lean) |
| **Verification** | `lake build` (Lean 4.36.0, stdlib only; 131-bank validity, 17-step endpoint test, and 171-step exclusion are kernel-checked; 156-step exhaustive closures and pairwise inequivalence use `native_decide`) |
| **Prior-art status** | Checked **24 November 2026**: Orland et al. published the 131 classes of length 191 and noted no 1-step extension exists; Kunt–Koch–Park also identify dimension 9 as the smallest open case. See [PRIOR_ART.md](../PRIOR_ART.md#nine-bit-snake-in-the-box). |

## Lean results

* **Prefix closure at step 156 (`Snake.bank_no_192`, `Snake.bank_no_new_191`):** take any of the 131 published 191-step snakes, read from either end (262 oriented prefixes), and retain its first 156 steps. Exhausting every valid next bit flip proves that **no 36-step continuation (length 192) exists** ([Results.lean](Results.lean)) and **every 35-step continuation (length 191) is equivalent to one of the 131 published classes** under reversal, coordinate permutation, and coordinate bit-flips ([Closure.lean](Closure.lean)).
* **Kernel-checked 171-step exclusion ([KernelChecks.lean](KernelChecks.lean)):** Lean's kernel directly checks the validity of all 131 published snakes and excludes any 192-step continuation when the first 171 steps are retained (without `native_decide`).
* **A fast test for a new 191-step class (`Snake.outside_bank_of_end_profiles`, [EndProfiles.lean](EndProfiles.lean), [Closure.lean](Closure.lean)):** starting from each end of a snake, record the Hamming distances from that endpoint after steps 1 through 17. Reversing the path swaps the two lists while hypercube symmetries preserve them. Lean's kernel verifies that all 131 published snakes have **unequal** endpoint lists; therefore any valid 191-step snake in $Q_9$ whose forward and backward 17-step distance profiles agree is provably inequivalent to all 131 published records.

## Build

Run from this directory with Lean **4.36.0** (standard library only):

```sh
lake build
```

## References

* [Orland et al., `arXiv:2607.15270v3`, §8](https://arxiv.org/html/2607.15270v3#S8) · [Pinned published data (`Math-AI-Caltech/Snake-in-the-Box`)](https://github.com/Math-AI-Caltech/Snake-in-the-Box/tree/46c765399353a588ea50444a5d6610f53102b1c2)
* [Kunt, Koch, and Park, `arXiv:2611.25268`](https://arxiv.org/abs/2611.25268)
* [Transition sequences](Bank.lean) · [Dated prior-art audit](../PRIOR_ART.md#nine-bit-snake-in-the-box)
