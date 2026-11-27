# Covering every trio among 14 people

**The minimum is 25 six-person groups.** With 24 groups, the maximum is 363 of the 364 trios. The first 24 lines of the group list miss only $\{1,4,8\}$. The last group covers it. [Group list](groups.txt)

## Why 24 groups fall short

Fix Alice. In each of her groups she has five companions. To cover every trio containing Alice, those five-person sets must cover every pair among the other 13 people. Both C++ verifiers check directly that nine five-person sets never suffice, so every person appears in at least ten groups. With 24 groups there are only $24\cdot6-14\cdot10=4$ spare places, so at most four people attend an eleventh group. [Pair-covering reference](https://ljcr.dmgordon.org/cover/show_cover.php?k=5&t=2&v=13)

Choose someone who attends exactly ten groups. Up to renaming the people, there are 30 possible schedules for that person. In any ten five-person sets covering all pairs of 13 people, each person appears at least three times to meet all 12 others. Their appearances total 50, so at least two people appear exactly three times, each meeting four distinct companions per appearance. These two share one set and fix five of the ten sets. The verifier labels those five and enumerates the remaining five, proving both that nine sets are impossible and that exactly 30 isomorphism classes occur at ten sets.

Fix one of the 30 starting schedules and list possible ten-group schedules for the other people. Two people must agree on exactly which groups they share. If a candidate has no matching schedule at each of five other people, all five would need an eleventh group, so discard that candidate. If five people run out of candidates, discard the starting schedule as well. Restricting this test to people sharing at least four groups with the starting person only weakens it.

A complete cover would preserve its own schedules at every step. Three rounds leave **13, then 5, then 0** of the original 30 types. This rules out 24 groups. [Exhaustive verifier](verify_covering.cpp)

The independent verifier uses individualization-refinement canonicalization, explicitly enumerates which four people may use the spare places, and runs exact backtracking on compatible schedules. Its 16 surviving assignments each force all 24 groups and miss two trios. Both lower-bound checks are self-contained compiled C++ with no external inputs. [Independent verifier](verify_independent.cpp)

## Reproduce

Run from this directory with a C++23 compiler (also valid C++20).

```sh
build_dir=$(mktemp -d)
c++ -std=c++23 -O3 verify_covering.cpp -o "$build_dir/verify_covering"
"$build_dir/verify_covering"
c++ -std=c++23 -O3 verify_independent.cpp -o "$build_dir/verify_independent"
"$build_dir/verify_independent"
```

The following Python check verifies the 25-group construction and identifies the missing trio in its 24-group prefix.

```python
from itertools import combinations
from pathlib import Path

people = set(range(1, 15))
groups = [
    frozenset(map(int, line.split()))
    for line in Path("groups.txt").read_text().splitlines()
]
assert len(groups) == len(set(groups)) == 25
assert all(len(group) == 6 and group <= people for group in groups)
trios = set(combinations(sorted(people), 3))
for group in groups[:24]:
    trios.difference_update(combinations(sorted(group), 3))
assert trios == {(1, 4, 8)}
trios.difference_update(combinations(sorted(groups[24]), 3))
assert not trios
```
