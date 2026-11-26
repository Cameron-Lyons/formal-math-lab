# How many cards can three stacks in series sort?

The smallest unsortable deck has **20 or 21 cards** by a computer-assisted bound. Cards move from the input through three last-in-first-out stacks in sequence. Each move sends one card one step to the right, and the output must be increasing. Lean proves the 21-card upper bound unconditionally. The 19-card exhaustive computation supplies one explicit premise of the Lean lower bound. [Theorems](ThreeStacks/Bounds.lean) · [Coverage premise](ThreeStacks/Coverage.lean)

Vatter’s Question 5.4 asks for the shortest unsortable permutation. His November update reports Pantone and Vatter’s bounds of 17 and 21. Their 21-card obstruction in arrival order is shown below. [Question and update](https://arxiv.org/html/2602.16355v4) · [MathFest slides](https://vincevatter.com/talks/2026-mathfest-stacks/) · [Prior-art note](../PRIOR_ART.md#three-stacks-in-series)

```text
6 3 12 8 17 5 2 11 7 19 14 10 4 18 13 21 16 9 20 15 1
```

## What Lean checks

- **The 21-card obstruction.** A physical run gives two intermediate card orders. No single stack can receive a triple in the order `a,b,c` and emit it as `c,a,b`. Lean derives a contradiction from the resulting constraints on the intermediate orders. It also replays sorting schedules for all 21 single-card deletions. [Physical theorem](ThreeStacks/Upper.lean) · [Forbidden triple](ThreeStacks/OneStack.lean) · [Order certificate](ThreeStacks/Certificate.lean) · [Deletion schedules](ThreeStacks/Saved.lean)
- **The lower bound.** If every 19-card deck sorts, every shorter deck sorts. Pad the deck with larger cards, sort, then erase the added cards’ moves. Lean proves this reduction and the reduction to decks ending in 1. The external enumeration covers all $18! = 6{,}402{,}373{,}705{,}728{,}000$ such decks. Lean replays the 384 final schedules and proves the soundness of joining stack configurations, taking the sorting dual and contracting consecutive descending cards. The assertion that these certificates cover the remaining decks is `ThreeStacks.Bulk19Coverage`. [Short proof](ThreeStacks/Bounds.lean) · [Normalization](ThreeStacks/Normalize.lean) · [Certificate soundness](ThreeStacks/Coverage.lean)

## Reproduce

Run from this directory with the pinned Lean 4.36.0 toolchain. The build uses the Lean standard library and includes the generated proof terms.

```sh
lake build
printf '%s\n' 'import ThreeStacks' '#check ThreeStacks.published_no_physical_run' \
  '#check ThreeStacks.published_deletion_sorts' '#print ThreeStacks.Bulk19Coverage' \
  '#check ThreeStacks.smallest_of_bulk_coverage' | lake env lean --stdin
```

The separate computation archive contains the search sources, group ledgers, individual schedules and the SAT refutation. The following commands audit its saved records using Python. To regenerate the full 19-card search, follow `coverage/ordered19.md` inside the archive. [Audit totals](evidence/n19-audit.json) · [Computation archive](evidence/three-stack-bound-proof.tar.gz)

```sh
work=$(mktemp -d)
tar -xzf evidence/three-stack-bound-proof.tar.gz -C "$work"
evidence="$work/three-stack-bound"
python3 "$evidence/coverage/audit18.py"
python3 "$evidence/coverage/audit19.py"
python3 "$evidence/verify/replay.py"
```

To regenerate the Lean certificates as well, use the same work directory. The order proof uses `drat-trim` with LRAT output. Both comparisons should report identical files. [Schedule generator](verify/build_witnesses.py) · [Order proof generator](verify/generate_order_proof.py)

```sh
python3 verify/build_witnesses.py --evidence-root "$evidence" "$work/Witnesses.lean"
cmp ThreeStacks/Data/Witnesses.lean "$work/Witnesses.lean"
drat-trim "$evidence/verify/published/pv21.cnf" "$evidence/verify/published/pv21.drat" -L "$work/pv21.lrat"
python3 verify/generate_order_proof.py --evidence-root "$evidence" "$work/pv21.lrat" "$work/OrderProof"
diff -qr ThreeStacks/OrderProof "$work/OrderProof"
```
