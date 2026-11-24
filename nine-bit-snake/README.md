# Can a nine-bit snake take 192 steps?

A snake is a sequence of distinct nine-bit strings. Consecutive strings differ in one bit, and all other pairs differ in at least two. Orland and coauthors published 131 inequivalent snakes of 191 steps each. They ask whether a 192-step snake exists, or whether another 191-step class can be found. Both questions remain open in this project. [Paper, §8](https://arxiv.org/html/2607.15270v3#S8) · [Published data at the revision used here](https://github.com/Math-AI-Caltech/Snake-in-the-Box/tree/46c765399353a588ea50444a5d6610f53102b1c2)

## Results

- **Keeping the first 156 steps.** Read any published snake from either end and keep its first 156 steps. Every valid 35-step continuation gives a published snake up to reversal, coordinate permutation, and coordinate flips. No valid 36-step continuation exists. Lean checks every legal next bit flip. The theorems are `Snake.bank_no_new_191` and `Snake.bank_no_192`. [191-step classification](Closure.lean) · [192-step exclusion](Results.lean)
- **A test for a new class.** Starting at each end, record the Hamming distances from that endpoint after steps 1 through 17. Reversing the path swaps the lists, and permuting or flipping coordinates preserves the distances. All 131 published snakes have unequal lists. By `Snake.outside_bank_of_end_profiles`, a valid 191-step snake with equal lists would give a new class. [Endpoint check](EndProfiles.lean) · [Novelty theorem](Closure.lean)

## Build

Run `lake build` in this directory with Lean 4.36.0. The project uses the standard library. The 156-step results and pairwise inequivalence check use `native_decide`. Lean's kernel checks the validity of all 131 records, the 17-step endpoint test, and a separate 192-step exclusion after retaining 171 steps. [Kernel checks](KernelChecks.lean) · [Transition sequences](Bank.lean)
