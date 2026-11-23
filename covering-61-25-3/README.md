# Can 26 groups of 25 cover every triple of 61 people?

The published example uses 27 groups. The 26-group candidate here misses exactly 84 of the 35,990 triples. Whether 26 groups suffice remains open in this work. [Published groups](https://kaust-a-laut.github.io/results/covering-C61-25-3-27/README.md) · [Lean check of the 84 triples](Covering.lean)

## What can be proved

**A 26-group cover can keep at most 20 of the 27 published groups.**

Suppose it kept 21. Its five other groups would have 125 seats between them and would have to cover every triple missed by those 21. There are exactly 296,010 ways to choose the 21. The following counting test rules out every choice.

1. **Count the seats people need.** If a pair still needs to meet *d* different third people, the pair must occur together at least ⌈*d*/23⌉ times. Each appearance of one person accounts for at most 24 such pair meetings. Two people who appear in *s* and *t* of five groups must share at least *s* + *t* − 5 groups. For someone appearing twice, two companions exclusive to opposite groups cannot form a missing triple with that person. Applying these bounds leaves 1,388 choices.
2. **Use the people who appear once.** All of a person's partners in missing triples must fit in their one group. Two such people who share a missing triple force the same group. Every extra appearance uses a spare seat, so we can enumerate who might appear more than once. For each choice, try every placement of the forced sets in five groups and count the seats again. Zero choices survive.

In that last count, a pair already in a forced group must meet again if its missing third people cannot all fit there. A forced group of exactly 25 is known in full, so we can cross off its triples and repeat the first step for the four remaining groups.

## Reproduce the checks

From this directory, run the Lean proofs with one command. The project pins Lean 4.36.0 and uses its standard library.

```sh
lake build
```

The main Lean theorem checks that the list of surviving choices is empty. The argument that every possible completion passes the tests is given above and in the implementation. For the 26-group candidate, Lean proves directly that any two replacement groups would need at least 52 seats. They have only 50. [Main theorem](RepairSearch.lean) · [Counting test](RepairCount.lean) · [Two-replacement proofs](Repairs.lean)

The independent C++ program prints the intermediate counts. [Source](SixGroupSearch.cpp)

```sh
c++ -std=c++20 -O3 SixGroupSearch.cpp -o six-group-search
./six-group-search Covering.lean
```
