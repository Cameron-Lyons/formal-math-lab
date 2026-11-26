# Covering every trio among 14 people

**The minimum is 25 six-person groups.** With 24 groups, the maximum is 363 of the 364 trios. The first 24 lines of the group list miss only $\{1,4,8\}$. The last group covers it. [Group list](groups.txt)

## Why 24 groups fall short

Fix Alice. In each of her groups she has five companions. To cover every trio containing Alice, those five-person sets must cover every pair among the other 13 people. This requires at least ten sets. Thus all 14 people need ten appearances apiece. With 24 groups there are only $24\cdot6-14\cdot10=4$ spare places. At most four people can attend an eleventh group. [Pair-covering bound](https://ljcr.dmgordon.org/cover/show_cover.php?k=5&t=2&v=13)

Choose someone who attends exactly ten groups. Up to renaming the people, there are 30 possible schedules for that person. To enumerate them, observe that each of the other 13 people must appear at least three times in the ten five-person sets to meet all 12 others. Their appearances total 50, so at least two people appear exactly three times. Each one meets four different companions at each appearance. In particular, these two meet exactly once, so their schedules fix five of the ten sets. The verifier labels these five and enumerates the remaining five.

Fix one of the 30 starting schedules and list possible ten-group schedules for the other people. Two people must agree on exactly which groups they share. If a candidate has no matching schedule at each of five other people, all five would need an eleventh group. Discard that candidate. If five people run out of candidates, discard the starting schedule as well. The verifier can restrict this test to people sharing at least four groups with the starting person.

A complete cover would preserve its own schedules at every step. Three rounds leave **13, then 5, then 0** of the original 30 types. This rules out 24 groups. [Exhaustive verifier](verify_covering.cpp)

The independent implementation enumerates which people may use the spare places and checks agreement directly. Its 16 surviving assignments each force all 24 groups. Each of those assignments misses two trios. Both lower-bound checks use compiled C++ and finite enumeration. [Independent verifier](verify_independent.cpp)

## Reproduce

Run from this directory with a C++20 compiler.

```sh
build_dir=$(mktemp -d)
c++ -std=c++20 -O3 verify_covering.cpp -o "$build_dir/verify_covering"
"$build_dir/verify_covering"
c++ -std=c++20 -O3 verify_independent.cpp -o "$build_dir/verify_independent"
"$build_dir/verify_independent"
```

The following Python check verifies the 25-group construction and identifies the missing trio in its 24-group prefix.

```python
from itertools import combinations
from pathlib import Path

people = set(range(1, 15))
groups = [frozenset(map(int, line.split())) for line in Path("groups.txt").read_text().splitlines()]
assert len(groups) == len(set(groups)) == 25
assert all(len(group) == 6 and group <= people for group in groups)
trios = set(combinations(sorted(people), 3))
for group in groups[:24]:
    trios.difference_update(combinations(sorted(group), 3))
assert trios == {(1, 4, 8)}
trios.difference_update(combinations(sorted(groups[24]), 3))
assert not trios
```
