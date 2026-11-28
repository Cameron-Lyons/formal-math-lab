# Checking marked cases at 125 members

What happens when we attack the conjectured boundary $t(16) = 124$ directly—trying to rule out an unrestricted 125-member family case by case? This note documents the partial elimination search across the **426 canonical root cases** induced by the 363-mask rank certificate, along with the replayable status ledger for the cases solved so far and those left open for resumption.

## The 426 root cases and current progress

By the [marked-set proof](rank-mark.md), any hypothetical admissible family $F$ of 125 subsets of $[16]$ has empty total intersection and contains **at least four marked members** from the fixed list of 363 masks (every marked set contains a seven-term progression, so has size at least 7). Partition all possibilities by the maximum size $m$ of a marked member in $F$:

- **Large singleton root ($m \ge 8$):** Fix a marked member of maximum size $m$. Identifying sets with their reflections ($i \mapsto 17 - i$) gives **178** canonical cases. (Other marked sets of size up to $m$ remain eligible.)
- **Seven-term quartet root ($m = 7$):** Every marked member is itself a seven-term progression; fix four distinct marked members. Among the 14 seven-term progressions, there are **248** pairwise-compatible quartets up to reflection.

That gives $178 + 248 = \mathbf{426}$ canonical cases in total. Current status recorded in the [case ledger](full-root-status.txt):

| Status | Cases | How handled |
| --- | ---: | --- |
| Closed by private-triple search (`closed`) | 78 | Excluded directly by `small_root_search.cpp` |
| Closed by large-member bound (`large`) | 13 | Root has size $\ge 13$, excluded by `large_members.cpp` |
| **Total excluded** | **91** | — |
| Pending (`open` / `budget`) | 335 | Recorded in `full-root-status.txt` for resumption |

## How the private-triple search works

The [replay program](small_root_search.cpp) uses the 504 private nonprogression triples ([shared implementation](private_triples.hpp)) to bound completions of each root case:

1. **Test the root pool directly.** First run the bounds below on the full candidate pool compatible with the fixed root(s).
2. **Eliminate nonprogression triples one by one.** Every 125-member family must contain at least one nonprogression triple ([compulsory triple proof](nonprogression-triples.md)). The program temporarily fixes each still-available nonprogression triple $T$ as an additional member. If fixing $T$ yields an upper bound below 125, $T$ is permanently deleted from the candidate pool for all subsequent tests in that case. If every nonprogression triple is eliminated, the case closes!

Each bound evaluation combines four constraints:

- **Five-element ceiling:** At most 93 members can have size $\ge 5$ ([five-element bound](five-or-more.md)). Applying the private-triple bound locally to the available size-$\ge 5$ candidates can tighten this ceiling further in a given case, forcing even more members of size $\le 4$.
- **Small-set floor:** At least 2 members must have size at most three ([four-element bound](four-or-more.md)).
- **Pool colorings:** Any valid completion must pick enough mutually compatible small candidates and enough marked candidates to satisfy the size and mark requirements. Partitioning each pool into classes of mutually incompatible candidates (each supplying at most one member) tests both requirements directly.
- **Iterative small-candidate pruning:** For each remaining candidate of size 2 through 4, fix it temporarily and run the localized private-triple budget from the [four-element proof](four-or-more.md#excluding-four-element-candidates)—pricing only nonprogression triples that intersect *every* currently fixed member of size at most four, and bounding low-cost discounts via incompatible color classes. Whenever the resulting upper bound is below 125, discard that candidate permanently and repeat until convergence.

## Case ID encoding and replay

Compile with a C++20 compiler from this directory. Each of the 426 canonical cases has a unique integer ID:

- **Singleton root ($m \ge 8$):** The case ID is simply the 16-bit numerical bit mask of the root (in the range $0$ through $65{,}535$, where bit $i$ represents element $i + 1$).
- **Seven-term quartet ($m = 7$):** Sort the 14 seven-term progressions by increasing bit mask (indices $0$ through $13$), encode the four chosen indices as a 14-bit signature (with 4 bits set), and add $65{,}536$. Between a quartet and its reflection, the canonical representative is whichever has the lexicographically smaller sorted list of four masks.

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic small_root_search.cpp -o /tmp/erdos272-roots
/tmp/erdos272-roots full rank.weights list
/tmp/erdos272-roots full rank.weights replay full-root-status.txt
/tmp/erdos272-roots full rank.weights 0 65535
/tmp/erdos272-roots full rank.weights 1400
```

**Understanding the commands and output:**

- `list` prints all 426 canonical case IDs.
- `replay full-root-status.txt` validates that the ledger contains every canonical case exactly once and reruns every case marked `closed`.
- A `large` entry in the ledger marks one of the 13 distinct root cases of size $\ge 13$, which are covered independently by the [large-member proof and verifier](README.md#excluding-large-members); the ledger checks the root size and counts these entries separately (run `large_members.cpp` to reproduce their exclusion).
- Passing a single numeric argument (like `1400`) or an inclusive range (`0 65535`) runs those case IDs directly. One *work unit* is one call to the private-triple bound; setting the work limit to `0` lets elimination run to completion.
- Each result line prints the case ID, final state, work units used, and number of nonprogression triples removed:
  - `closed`: a 125-member family is ruled out in this case.
  - `budget`: the work limit was reached before elimination finished.
  - `open`: elimination reached a fixed point with candidates still surviving.

## Intersections of length at most six

The same executable also supports the shorter-intersection computations:

- **`quartets` mode:** Takes the first four marked members (from the 101-mark list) in the enumerator's order, allowing all later marks of any size. The private-triple bound on eligible sets of size $\ge 5$ sets the required number of small sets; the checker then fixes individual nonprogression triples and re-checks the remaining pool after proved exclusions. See [short-intersections.md](short-intersections.md) for the proof and full replay command.
- **`short` mode:** Checks individual quartets of seven-term progressions under the length-$\le 6$ intersection restriction, using the same 248 quartet IDs as the unrestricted search:

```sh
/tmp/erdos272-roots short list
/tmp/erdos272-roots short 0 65551
```
