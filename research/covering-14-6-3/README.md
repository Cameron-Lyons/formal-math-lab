# Covering Every Trio Among 14 People: $C(14, 6, 3) = 25$

Suppose 14 people want to form 6-person committees so that **every possible 3-person trio** sits together on at least one committee. What is the smallest number of committees required? In combinatorial design theory, this minimum is the **covering number** $C(14, 6, 3)$ — the fewest $k$-element subsets ("blocks") of a $v$-element set that contain every $t$-element subset, here with $(v, k, t) = (14, 6, 3)$.

**The answer is exactly 25 six-person groups.** With 24 groups, you can cover at most **363 of the $\binom{14}{3} = 364$ trios** — always falling at least one trio short. The first 24 lines of [groups.txt](groups.txt) achieve that 363-trio maximum, missing only $\{1, 4, 8\}$, and the 25th group covers that final trio.

| | |
| --- | --- |
| **Result** | $C(14, 6, 3) = 25$; 24 groups cover at most 363 of 364 trios |
| **Upper bound (witness)** | 25 explicit 6-person groups in [groups.txt](groups.txt) (first 24 miss only $\{1, 4, 8\}$) |
| **Lower bound (no 24-cover)** | Self-contained C++ verifier: [verify_covering.cpp](verify_covering.cpp) |
| **Trust boundary** | Compiled C++20/C++23 exhaustive search with exact arithmetic (no external inputs; outside any proof-assistant kernel) |

---

## Why 24 groups fall short

### The big idea

Rather than searching directly over all choices of 24 committees (far too many to enumerate), we zoom in on **one person's schedule** — the list of groups that person attends.

1. First, a simple link to pair-covering shows that **every person must attend at least 10 groups**.
2. With only 24 committees of size 6, there are barely enough seats to give everyone 10 groups — leaving only **4 spare seats** across all 14 people. So at least 10 people attend *exactly* 10 groups, and at most 4 people can attend an 11th.
3. Up to renaming people, a 10-group person's schedule can take only **30 possible shapes**.
4. Checking whether the other people can consistently adopt compatible 10-group schedules — while respecting the budget of at most 4 "exception" people who take an 11th group — collapses all 30 shapes to **zero** in three quick rounds.

---

### Step 1: Every person attends at least 10 groups (leaving only 4 spare seats)

Fix one person, say Alice. In each committee Alice attends, she sits with 5 companions chosen from the remaining 13 people. For every trio containing Alice (that is, $\{\text{Alice}, x, y\}$) to be covered, Alice's committees — with Alice removed — must form a collection of 5-person sets covering **every pair** $\{x, y\}$ among the other 13 people.

Each 5-person set covers $\binom{5}{2} = 10$ of the $\binom{13}{2} = 78$ pairs, so you might hope 8 or 9 sets could work. However, the pair-covering number is $C(13, 5, 2) = 10$ ([pair-covering reference](https://ljcr.dmgordon.org/cover/show_cover.php?k=5&t=2&v=13)), and both C++ verifiers prove directly from scratch that **9 five-person sets never suffice**. Therefore:

- **Every person must appear in at least 10 groups.**
- Across 24 six-person groups, there are $24 \cdot 6 = 144$ total seats, while giving all 14 people 10 appearances already uses $14 \cdot 10 = 140$ seats.
- That leaves only

$$
24 \cdot 6 - 14 \cdot 10 = 4
$$

spare places, so **at most 4 people** can attend an 11th group (and at least 10 people attend *exactly* 10 groups).

---

### Step 2: Only 30 schedules exist for a 10-group person

Pick a "starting person" who attends **exactly 10 groups**, and remove them to obtain ten 5-person sets covering every pair among the other 13 people. How many ways can those 10 sets be arranged, up to renaming the 13 companions?

Count how often each of the 13 companions appears across the 10 sets:

- Each time a companion appears in a 5-person set, they meet 4 other people. To meet all 12 other companions, every person must appear at least $\lceil 12 / 4 \rceil = 3$ times.
- Total appearances across all 10 sets equal $10 \cdot 5 = 50$. If at most one companion appeared 3 times and the other 12 appeared at least 4 times, the total would be at least $3 + 12 \cdot 4 = 51 > 50$, which is impossible.
- Hence **at least two companions appear exactly 3 times**. Because $3 \cdot 4 = 12$, each of these two people must meet **4 distinct companions** on each of their three appearances (zero overlap between their sets).
- These two 3-appearance people must also meet *each other*, so they share **exactly 1** of the 10 sets, while their remaining appearances fill $2 + 2 = 4$ other sets.

Up to relabeling the people, those two companions completely **fix 5 of the 10 sets**. The verifier labels those 5 forced sets and exhaustively enumerates the remaining 5 sets, simultaneously proving:

1. **9 sets are impossible** (no valid completion exists with 9 sets), and
2. **Exactly 30 isomorphism classes** occur at 10 sets.

---

### Step 3: Three rounds of compatibility pruning eliminate all 30 types

Now fix one of the 30 possible 10-group schedules for our starting person, and for each of the other 13 people list every possible 10-group schedule they could hold.

Any two people's schedules must satisfy a basic consistency rule: **two people must agree on exactly which groups they share** (whenever person $A$'s schedule includes person $B$ in a specific set of groups, person $B$'s schedule must include person $A$ in those exact same groups).

We iteratively prune impossible schedules using the 4-spare-seat limit:

- **Candidate pruning:** If a candidate 10-group schedule for person $x$ has *no* matching 10-group schedule for at least **5** other people, then all 5 of those people would be forced into an 11th group — impossible with only 4 spare seats. Discard that candidate.
- **Starting-type pruning:** If **5** other people run out of surviving candidates altogether, all 5 would need an 11th group — impossible. Discard the starting schedule as well.
- To keep the test fast (and strictly sound), the verifier restricts the compatibility test to people sharing at least 4 groups with the starting person; dropping constraints on the remaining pairs only weakens the filter and can never discard a genuine cover.

In any genuine 24-group cover, the true 10-group schedules would survive every round of pruning. Running three rounds narrows the 30 starting types down to:

$$
30 \;\longrightarrow\; \mathbf{13} \;\longrightarrow\; \mathbf{5} \;\longrightarrow\; \mathbf{0}.
$$

No starting type survives, ruling out 24 groups completely ([verify_covering.cpp](verify_covering.cpp)).

---

## Reproduce

Run from this directory with a C++23 compiler (the code is also valid C++20):

```sh
build_dir=$(mktemp -d)
c++ -std=c++23 -O3 verify_covering.cpp -o "$build_dir/verify_covering"
"$build_dir/verify_covering"
```

The following Python snippet verifies the 25-group construction in [groups.txt](groups.txt) and confirms that its first 24 groups miss only `{1, 4, 8}`:

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

## References

- [La Jolla Covering Repository](https://ljcr.dmgordon.org/cover/show_cover.php?k=5&t=2&v=13) — pair covering $C(13, 5, 2) = 10$
