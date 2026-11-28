# How many cards can three stacks in series sort?

Imagine a shuffled deck of cards numbered $1, 2, \ldots, n$ arriving from the left, followed by **three stacks in series** (Stack 1, Stack 2, Stack 3) and an output pile on the right. Each stack is last-in, first-out (LIFO—you can only remove its top card), and every legal move sends one card one station to the right: input $\to$ Stack 1, Stack 1 $\to$ Stack 2, Stack 2 $\to$ Stack 3, or Stack 3 $\to$ output. A deck is **sortable** if some sequence of moves emits the cards in strictly increasing order $1, 2, \ldots, n$.

What is the length of the **shortest unsortable deck**? Vatter's Question 5.4 asks for this exact threshold, and his November update reports Pantone and Vatter's bounds of 17 (lower) and 21 (upper), using the 21-card obstruction (written in arrival order):

```text
6 3 12 8 17 5 2 11 7 19 14 10 4 18 13 21 16 9 20 15 1
```

This project tightens the window to **20 or 21 cards** by a computer-assisted bound:
- **Upper bound ($\le 21$, proved unconditionally in Lean):** Lean's kernel verifies that the 21-card deck above has no physical sorting run and that deleting any single card leaves a sortable 20-card deck.
- **Lower bound ($\ge 20$, conditional on one explicit coverage premise):** Every deck of length $\le 19$ is sortable, modulo one named Lean premise (`ThreeStacks.Bulk19Coverage`) asserting that the external exhaustive computation over all $18! = 6{,}402{,}373{,}705{,}728{,}000$ normalized 19-card decks covers all remaining cases.

[Theorems](ThreeStacks/Bounds.lean) · [Coverage premise](ThreeStacks/Coverage.lean) · [Question and update](https://arxiv.org/html/2602.16355v4) · [MathFest slides](https://vincevatter.com/talks/2026-mathfest-stacks/)

## What Lean checks (and where the trust boundary sits)

### 1. The 21-card obstruction (unconditional Lean kernel proof)

**The big idea.** As cards flow through three stacks in series, they pass through two intermediate linear orders:

$$
\text{Input} \xrightarrow{\text{Stack 1}} \text{Order 1} \xrightarrow{\text{Stack 2}} \text{Order 2} \xrightarrow{\text{Stack 3}} \text{Sorted output } (1, 2, \ldots, n).
$$

No single LIFO stack can receive three cards in the relative arrival order `a, b, c` and emit them as `c, a, b`: to emit `c` first, both `a` and `b` must remain inside the stack when `c` arrives, with `b` sitting *above* `a`, which forces `b` to exit before `a`.

Each of the three stack transitions therefore forbids turning any triple `a, b, c` into `c, a, b`. For Pantone and Vatter's 21-card deck, Lean replays a SAT-derived refutation certificate to prove that no two intermediate orders can satisfy all three forbidden-triple constraints (`ThreeStacks.published_no_physical_run`). Lean also replays explicit sorting schedules for all 21 single-card deletions (`ThreeStacks.published_deletion_sorts`), confirming that the obstruction is minimal.

[Physical theorem](ThreeStacks/Upper.lean) · [Forbidden triple](ThreeStacks/OneStack.lean) · [Order certificate](ThreeStacks/Certificate.lean) · [Deletion schedules](ThreeStacks/Saved.lean)

### 2. The 19-card lower bound (Lean reductions + explicit external coverage premise)

- **Proved in Lean:**
  - *Monotonicity:* If every 19-card deck sorts, then every shorter deck sorts—pad any shorter deck with larger cards, sort the 19-card deck, and erase the added cards' moves.
  - *Normalization:* It suffices to sort 19-card decks ending in card `1` (reducing the search space to $18! = 6{,}402{,}373{,}705{,}728{,}000$ decks).
  - *Schedule replay and structural soundness:* Lean replays all 384 final sorting schedules and proves the soundness of joining stack configurations, taking the sorting dual, and contracting consecutive descending cards.
- **External premise (`ThreeStacks.Bulk19Coverage`):** The single remaining claim—that the external exhaustive enumeration's certificates cover all $18!$ normalized 19-card decks—is isolated as the named premise `ThreeStacks.Bulk19Coverage`, audited externally via the Python scripts and computation archive below.

[Short proof](ThreeStacks/Bounds.lean) · [Normalization](ThreeStacks/Normalize.lean) · [Certificate soundness](ThreeStacks/Coverage.lean)

## Reproduce

### 1. Build and check the Lean proofs

Run from this directory with the pinned Lean 4.36.0 toolchain (Lean standard library only, including generated proof terms):

```sh
lake build
printf '%s\n' 'import ThreeStacks' '#check ThreeStacks.published_no_physical_run' \
  '#check ThreeStacks.published_deletion_sorts' '#print ThreeStacks.Bulk19Coverage' \
  '#check ThreeStacks.smallest_of_bulk_coverage' | lake env lean --stdin
```

### 2. Audit the external 19-card computation archive

The computation archive contains the search sources, group ledgers, individual sorting schedules, and the SAT refutation. These commands audit the saved records in Python (to regenerate the full 19-card search from scratch, follow `coverage/ordered19.md` inside the archive):

- [Computation archive](evidence/three-stack-bound-proof.tar.gz)

```sh
work=$(mktemp -d)
tar -xzf evidence/three-stack-bound-proof.tar.gz -C "$work"
evidence="$work/three-stack-bound"
python3 "$evidence/coverage/audit18.py"
python3 "$evidence/coverage/audit19.py"
python3 "$evidence/verify/replay.py"
```
