# Checking marked cases at 125 members

A putative admissible family of size 125 has at least four marked members. Fix one of maximum size if that size is at least eight. Otherwise fix four of its seven-term progressions. Reflection gives 178 cases of the first kind and 248 of the second. Other marks of the same cardinality remain eligible. Of these 426 cases, the private-triple search excludes 78, the independent large-member argument covers 13 further cases, and 335 remain pending in this search. [Case ledger](full-root-status.txt) · [Marked-set proof](rank-mark.md)

The [replay program](small_root_search.cpp) uses the 504 private nonprogression triples to bound the possible completions of the fixed root sets. It first tests the current candidate family. It then tries each possible nonprogression triple as an additional fixed member. A triple whose inclusion rules out 125 members can be removed from the candidate list for all subsequent tests. Once all such triples have been excluded, the case closes because every 125-family must contain one. [Compulsory triple proof](nonprogression-triples.md)

Each test uses the following bounds.

- At most 93 members have five or more elements. A second application of the private-triple bound to the available large candidates may lower this upper bound in a particular case. The remaining members must have at most four elements. [Five-element bound](five-or-more.md)
- At least two members have at most three elements. [Four-element bound](four-or-more.md)
- A completion must contain enough mutually compatible small candidates and enough marked candidates to meet both requirements. Partitioning each pool into classes of mutually incompatible candidates tests these requirements.
- For each remaining candidate of size two through four, fix it temporarily and apply the same private-triple budget used in the four-element proof. Price only triples meeting every fixed member of size at most four. The total discount is bounded by partitioning the low-cost candidates into classes of incompatible sets. Remove a candidate if the resulting bound is below 125. Repeating this step can remove further candidates. [Private-triple argument](four-or-more.md#excluding-four-element-candidates) · [Shared implementation](private_triples.hpp)

## Replay

Compile with a C++20 compiler in this directory. An unrestricted singleton-root ID is its numerical mask. For a quartet, sort the fourteen seven-term progressions by increasing mask, encode the indices of the four selected ones as a 14-bit signature, and add 65,536. A quartet and its reflection use the lexicographically smaller of the two sorted lists of four masks.

```sh
c++ -O3 -std=c++20 -Wall -Wextra -Werror -pedantic small_root_search.cpp -o /tmp/erdos272-roots
/tmp/erdos272-roots full rank.weights list
/tmp/erdos272-roots full rank.weights replay full-root-status.txt
/tmp/erdos272-roots full rank.weights 0 65535
/tmp/erdos272-roots full rank.weights 1400
```

The replay command validates that the ledger contains every canonical case exactly once and reruns every case marked closed. A `large` entry is a distinct case covered by the independent exclusion of members of size 13 or greater. The ledger checks the size and counts these entries separately. Run the large-member verifier to reproduce their exclusion. [Large-member proof and verifier](README.md#excluding-large-members) The optional numerical case arguments are either a single ID or inclusive lower and upper IDs. One work unit is one call to the private-triple bound. A work limit of zero allows the elimination to run to completion. Each result gives the case ID, state, work used and number of nonprogression triples removed. A `closed` result excludes a 125-family in that case. The state `budget` records a reached work limit. The state `open` means elimination reached a fixed point with candidates still present.

## Intersections of length at most six

In `quartets` mode the checker takes the first four marked members in the order supplied by the enumerator. It allows all later marks, of any size. The private-triple bound on the eligible large sets gives the number of small sets needed. The checker tries fixing individual nonprogression triples and also tests the candidates left after the proved exclusions. [Proof and full replay](short-intersections.md)

The `short` mode below checks individual quartets of seven-term progressions, using the same 248 IDs as the unrestricted search.

```sh
/tmp/erdos272-roots short list
/tmp/erdos272-roots short 0 65551
```
