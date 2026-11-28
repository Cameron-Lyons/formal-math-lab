# Exact three-stack verification

The unrestricted minimum is 20 or 21 by the local computer-assisted results. The complete length-19 computation sorted every permutation. For the upper bound, the independent SAT certificate proves that the published 21-card deck is unsortable. Each of its 21 one-card deletions has a sorting schedule. [Length-19 proof](../coverage/ordered19.md) · Complete audit (`coverage/results/n19-audit.json` in `results.tar.gz`) · [Pantone and Vatter’s MathFest slides](https://vincevatter.com/talks/2026-mathfest-stacks/)

## Why two intermediate orders suffice

Let $P$ be the input order, $A$ the order of cards leaving the first stack, $B$ the order leaving the second stack, and $I$ the increasing order. A full run provides three one-stack transitions from $P$ to $A$, from $A$ to $B$, and from $B$ to $I$. Conversely, suppose these three transitions are feasible. Whenever a downstream stack needs another input card, ask the preceding stack to supply its next card. This recursive scheduling realizes all three transitions in series. The function `operation_word` implements this construction.

For a single stack, a transition from $U$ to $V$ is possible exactly when there is no triple of distinct cards with order $a,b,c$ in $U$ and order $c,a,b$ in $V$. Such a triple is impossible because $b$ must still be sitting above $a$ when $c$ leaves. For the converse, pop each next requested card as soon as it is exposed, reading input as needed. At the first failure the requested card $a$ is buried under some $b$. The earlier request that caused the machine to read $b$ was for a card $c$ farther along in the input, since $b$ remained in the stack. These cards give the forbidden triple.

In `check.py`, one Boolean for each unordered pair records its order in $A$, and a second Boolean records its order in $B$. The two directed-cycle clauses for each triple in each order enforce transitivity. The remaining clauses forbid the triple transition just proved impossible. A fixed input or output contributes one clause per unordered triple. The middle transition contributes one per ordered triple. Thus a deck of length $n$ gives $2\binom{n}{2}$ variables and $12\binom{n}{3}$ clauses. The 21-card instance has 420 variables and 15,960 clauses.

## Verify the 21-card certificate

The supplied DIMACS formula and DRAT refutation were generated independently of the authors. The proof checker reports `s VERIFIED`. Run these commands from the project root. Only the final replay command requires Python.

```sh
git clone https://github.com/marijnheule/drat-trim.git /tmp/three-stack-proof-tool
git -C /tmp/three-stack-proof-tool checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
cc -O2 -std=gnu17 /tmp/three-stack-proof-tool/drat-trim.c -o /tmp/three-stack-proof-tool/drat-trim
/tmp/three-stack-proof-tool/drat-trim verify/published/pv21.cnf verify/published/pv21.drat
python3 verify/replay.py
```

The last command independently replays all 21 deletion schedules in `published/deletions.txt`. In each word, 1 moves the next input card onto stack 1, 2 moves from stack 1 to 2, 3 moves from stack 2 to 3, and 4 moves from stack 3 to the output. The replayer checks every move, all final stack contents, and the full output order.

To regenerate the formula, refutation, and schedules, install PySAT in a virtual environment. The run here used Python 3.15 and python-sat 1.9.dev25. [PySAT](https://pysathq.github.io/)

```sh
python3 -m venv /tmp/three-stack-python
/tmp/three-stack-python/bin/pip install 'python-sat==1.9.dev25'
/tmp/three-stack-python/bin/python verify/check.py --certificate /tmp/pv21 --deletions \
  6 3 12 8 17 5 2 11 7 19 14 10 4 18 13 21 16 9 20 15 1
cmp /tmp/pv21.cnf verify/published/pv21.cnf
/tmp/three-stack-proof-tool/drat-trim /tmp/pv21.cnf /tmp/pv21.drat
```

## Two finite searches at length 20

* For each deletion of one card from the published 21, relabel its remaining cards consecutively in rank order. Permute the values at up to four positions. Each deletion gives 46,076 cases, including the unchanged ordering. Across all deletions this gives 967,596 visits and **955,134 distinct** 20-card decks.
* Delete any two cards from the published 21. Insert a new card at any position and any rank, after standardizing the 19 remaining cards. There are 84,000 visits before deduplication and **74,793 distinct** 20-card decks.

The two families share 8,590 decks. Their union has **1,021,337 distinct decks**, all sortable. Each fresh SAT solution supplies a four-move-per-card word which is replayed. For nearby inputs, the search also reuses a previously verified pair of intermediate orders when a direct one-stack simulation can deliver the new input to its first intermediate order.

```sh
/tmp/three-stack-python/bin/python verify/neighborhood.py
/tmp/three-stack-python/bin/python verify/extensions.py
/tmp/three-stack-python/bin/python verify/extensions.py --counts-only
```

The first command can be split into disjoint deletion-position ranges with `--first 1 --last 11` and `--first 12 --last 21`. The recorded outputs are in `published/four-position-results.txt` and `published/extension-results.txt`.

## Prefix and continuation tables

For the length-17 search, `layout_audit.cpp` independently reconstructs a literal move word for each claimed prefix layout. It starts from the proposed three stacks, works backwards to the input, then replays the word forwards and compares all three stacks. It checks every accepted layout for every prefix through length 7 and 512 seeded samples of length 10. At length 7 all 566,887 accepted layouts replayed. The ten-card samples contributed 86,255 successful replays.

The same program checks the lookup of every valid continuation-table configuration with up to six ordinary unread cards and the final minimum. It initializes the first two physical stacks with the indicated parked cards and tests whether they can emit the active cards in order. The table with six ordinary cards contains 131,760 valid configurations, including 56,440 positive entries. All verdicts agreed with the physical solver and every positive word replayed.

```sh
g++ -std=c++20 -O3 verify/layout_audit.cpp -o /tmp/three-stack-layout-audit
/tmp/three-stack-layout-audit
```

The recorded counts are in `layout-audit-results.txt`.

## Independent exhaustive join at length 17

Use the binary prefix and suffix tables built in `coverage/`. Each prefix order supplies a bitmask of achievable layouts. Each suffix order and value set supplies a bitmask of layouts with a verified continuation. A shared bit certifies the entire deck.

The independent checker groups suffixes by identical masks and finds the inclusion-minimal masks among them. A prefix disjoint from a mask must be disjoint from each of its subsets. Assign each distinct suffix mask to a contained minimal mask, enumerate all its candidate prefix ranks, and compare both full masks. This directly enumerates every disjoint pair. Its input consists of the same two tables as the primary join, and it uses its own enumeration, rank conversion, and disjoint-pair algorithm.

| Count | Length 17 |
|---|---:|
| End-in-1 decks | 20,922,789,888,000 |
| Distinct tail masks | 250,804 |
| Inclusion-minimal tail masks | 375 |
| Decks disjoint in the direct join | 63,677,015 |
| Disjoint decks with a contractible descending consecutive pair | 9,199,295 |
| Additional decks covered after taking the sorting dual | 54,459,680 |
| Explicit residual sorting schedules | 18,040 |

The two joins produced identical residual sets. Independent SAT runs and physical replays sorted all 18,040 residual decks. In the commands below, set `prefix_table` and `tail_table` to the 17-card table paths.

```sh
g++ -std=c++20 -O3 -march=native verify/join_audit.cpp -o /tmp/three-stack-join-audit
/tmp/three-stack-join-audit "$prefix_table" "$tail_table" /tmp/residual-17.txt
python3 verify/residual_words.py replay /tmp/residual-17.txt verify/n17-residual-words.gz
```

For a deck whose minimum is earlier, swap it with the final card $x$. Given a sorting schedule for the resulting end-in-1 deck, remove all moves of those two cards from that schedule. At its original input move for $x$, pass the real 1 directly through the three stacks. At its original output move for $x$, pass the real final $x$ directly through. At the first replacement no other output has occurred, since the swapped deck’s 1 is still unread. At the second replacement all other input has been read, since that 1 has already left. Every other stack move remains legal. This extends the end-in-1 result to all 17-card decks.

The same checker supports a sampled suffix-order range at length 18. It memory-maps both tables read-only, groups equal suffix masks within each shard, and materializes the disjoint prefix ranks for one contained minimal mask at a time. The optional arguments are the first rank, excluded upper limit, stride, and maximum ranks per shard. A dash as the output path suppresses residual rows while retaining exact counts.

```sh
g++ -std=c++20 -O3 -march=native -DCARD_COUNT=18 verify/join_audit.cpp -o /tmp/three-stack-join-audit18
/tmp/three-stack-join-audit18 "$prefix_table" "$tail_table_18" - 37 5040 97 8
```

This covers 52 of 5,040 suffix ranks. Its counts are in `n18-join-sample.txt`.

At length 19 use an 11-card prefix and compile with `-DCARD_COUNT=19`. A shared, file-backed index stores the lexicographic prefix permutations and a transpose of the 353 layout bits. The transpose records, for each layout, the exact set of prefix ranks that can produce it. Workers verify that the index matches the entire input prefix table. Build it once and pass the same file to each worker.

```sh
g++ -std=c++20 -O3 -march=native -DCARD_COUNT=19 verify/join_audit.cpp -o /tmp/three-stack-join-audit19
/tmp/three-stack-join-audit19 --build-index "$prefix_table_11" "$shared_prefix_index"
/tmp/three-stack-join-audit19 "$prefix_table_11" "$tail_table_19" - 53 5040 1151 1 "$shared_prefix_index" canonical
```

The final option selects the lexicographically smaller representative of a deck and its sorting dual. This relation preserves sortability and the final minimum, so checking one representative per pair suffices when the full domain is eventually covered. The count labeled `By symmetry` identifies rows assigned to their other representative. Omit `canonical` to retain every residual row for direct comparisons between joins.

## Dual addresses from two factorial codes

For a normalized prefix permutation of length $k$, let $u_v$ count the larger ranks before rank $v$, and let $s_v$ count the smaller ranks before $v$. Store two integers
$H=\sum_v u_v (k-1-v)!$ and $L=\sum_v s_v v!$.
When $d$ smaller ranks are removed, $H\bmod (k-d)!$ is the same code for the retained larger ranks. Their digits count larger predecessors, which have all been retained. The removed digits contributed multiples of $(k-d)!$. Likewise $L\bmod d!$ codes the $d$ smaller ranks alone.

At a fixed suffix order and value set, these restrictions give the orders of the high and low original prefix subsequences. Small lookup tables convert their factorial codes into the variable parts of the dual prefix and suffix ranks. For the dual suffix value set we also need the original positions of the $d$ low ranks. Our byte-packed threshold comparison extracts that mask in two machine words. The baseline encoder in `coverage/quadrant.hpp` computes the same ranks by scanning the prefix. At length 20 the accelerated encoder uses this baseline for geometries having 11 high ranks and one low rank.

The test directly constructs the full deck and dual, then ranks the dual prefix, suffix order, and suffix value set. It compares all three addresses against both implementations. The test includes every possible number of low ranks, all threshold masks, and a timing run in which the direct and two optimized implementations must produce identical checksums.

```sh
g++ -std=c++20 -O3 -march=native verify/quadrant_codes_test.cpp -o /tmp/three-stack-quadrant-codes-test
/tmp/three-stack-quadrant-codes-test
```

An optional shared file holds the two 32-bit codes per prefix rank, in lexicographic order. Workers can also encode each surviving prefix directly. The Linux file builder checks a deterministic sample against independently unranked prefix permutations after generation. Supply a new destination path.

```sh
g++ -std=c++20 -O3 -march=native verify/build_quadrant_codes.cpp -o /tmp/three-stack-build-quadrant-codes
/tmp/three-stack-build-quadrant-codes 11 "$prefix_codes_file"
```

## Independent packed-file verification at length 20

Each suffix order has a dictionary of complete 421-column masks and an array of 16-bit identifiers indexed by suffix value set. A separate streaming parser recomputes the dimensions, validates every extent and dictionary identifier, and compares every reconstructed row directly to the raw input. All 253,955,520 comparisons passed. The raw file contains 14,221,509,120 bytes and the packed file contains 4,204,212,112 bytes. The recorded result is in `n20-tail-comparison.txt`.

```sh
g++ -std=c++20 -O3 -march=native -DCARD_COUNT=20 verify/pack_tail.cpp -o /tmp/three-stack-pack-tail20
/tmp/three-stack-pack-tail20 "$tail20_raw" "$tail20_packed"
g++ -std=c++20 -O3 -march=native verify/check_packed_tail.cpp -o /tmp/three-stack-check-packed-independent
/tmp/three-stack-check-packed-independent 20 12 "$tail20_raw" "$tail20_packed"
```

For accelerated dual cut checks, `select_dual_projection.cpp` chooses up to 64 of the existing layout columns. Its training and holdout sets use disjoint dual prefix ranks. It can also evaluate a previously selected list on independent deferred-query spools. Scoring evaluates each candidate prefix layout directly and intersects it with the actual continuation mask. Projecting both masks onto the same original column IDs makes any resulting match a sufficient certificate. A miss can proceed to the full-mask check. The file uses 8 bytes per prefix, or 3,832,012,928 bytes including its header for all 12-card prefixes.

```sh
g++ -std=c++20 -O3 -march=native verify/select_dual_projection.cpp -o /tmp/three-stack-select-dual-projection
/tmp/three-stack-select-dual-projection "$tail20_packed" 100000 "$training_spool" > "$score_report"
awk '$2=="column" {print $3}' "$score_report" > "$column_ids"
/tmp/three-stack-select-dual-projection "$tail20_packed" 100000 --columns "$column_ids" "$validation_spool"
g++ -std=c++20 -O3 -march=native verify/project_prefix.cpp -o /tmp/three-stack-project-prefix
/tmp/three-stack-project-prefix build 12 "$prefix_slice" "$column_ids" "$projected_slice" "$first_rank"
/tmp/three-stack-project-prefix verify 12 "$prefix_slice" "$column_ids" "$projected_slice" "$first_rank"
```

The projection verifier checks every stored bit against independent column-by-column extraction. The x86 implementation uses BMI2 parallel extraction when enabled at compilation. The scalar implementation builds from the same source on other CPUs.

The 19- and 20-card sampled selections are stored in `n19-projection-columns.txt` and `n20-projection-columns.txt`. Separate runs on untouched source prefix intervals are summarized in `projection-benchmarks.txt`. At length 19 the 64 columns captured 70,022 of 71,261 full-cut positives in 72,000 deferred queries. At length 20 they captured 41,047 of 41,911 full-cut positives in 42,521 deferred queries. These are sampled measurements for choosing the projection.

The GPU export stores one native 64-bit word per full prefix row and one per packed dictionary entry. Its two output files contain raw words with zero payload offset. Each word orders its bits by ascending original layout ID. The existing packed continuation file supplies the order offsets and local dictionary IDs. Every output word is expanded back onto its selected source columns and compared during export.

```sh
g++ -std=c++20 -O3 -march=native -DCARD_COUNT=19 verify/project_gpu_tables.cpp -o /tmp/three-stack-project19-gpu
/tmp/three-stack-project19-gpu verify/n19-projection-columns.txt "$prefix11" "$tail19_packed" "$gpu_prefix" "$gpu_dictionary"
```

## Certified continuation groups at length 19

For the 11-card cut, each positive continuation has seven positions, occupied by distinct labels from 1 through 18. A group fixes all placements of labels 1 through 7. Let $S$ be the subset of these small labels present. Read them in increasing numerical order. Record each small label’s position as its rank among the still vacant positions, starting at zero. Accumulate these digits in radices $7,6,\ldots$. For an integer mask $S$ with bit $v-1$ for label $v$, its base offset is the sum of $7!/(7-|T|)!$ over all masks $T<S$. The group ID is the offset plus the accumulated positional rank. There are 130,922 such groups.

If $b=7-|S|$, a group has exactly $11!/(11-b)!$ distinct assignments to its empty positions. Intersecting the full continuation masks over a group yields layouts valid for every assignment. The refinement fixes the position of the largest card in the positive continuation. For $b>0$, each of the $b$ free positions is occupied by the maximum on exactly $11!/((11-b)!b)$ rows. For $b=0$ the sole row fixes the maximum. Empty children are encoded by zero masks and an explicit validity bitmap.

Under the sorting dual, a small card with value $v$ at original positive suffix position $j$ becomes small value $7-j$ at dual positive suffix position $7-v$. Hence there is an involution of the group IDs. It computes the group of the dual suffix directly from the original suffix, for every choice of the preceding standardized head.

The builder verifies the exact bitwise intersections independently against all 160,392,960 original rows and checks each group’s cardinality. It separately verifies the permutation of group IDs and compares it with explicit reconstruction of 1,290,240 full decks and their duals. The reproducible outputs are raw native little-endian vectors. `group-and.u64` has shape 130922×6. `group-and-by-largest-position.u64` has shape 130922×7×6. Both full-mask representations use the same six words as the original 353-column table. `largest-position-valid.u8` provides one seven-bit validity mask per group. The two 5040×128 unsigned 32-bit directories convert a suffix order and its small-value mask to its own group or its dual’s group.

```sh
g++ -std=c++20 -O3 -march=native -DCARD_COUNT=19 verify/build_tail_fibers.cpp -o /tmp/three-stack-build-tail19-fibers
/tmp/three-stack-build-tail19-fibers "$tail19_packed" "$tail19_raw" "$new_group_dir"
/tmp/three-stack-build-tail19-fibers "$tail19_packed" "$tail19_raw" "$new_group_dir" largest
/tmp/three-stack-build-tail19-fibers --reflect "$new_group_dir"
```

## Targeted searches for a shorter obstruction

The exhaustive length-19 calculation left 384 decks for its final individual test. Inserting one card at every possible position and rank into each of them and their reflected decks gives 259,147 distinct length-20 permutations. The end-card swap and reflection reduce this family to 116,599 test inputs. The verification replayed 106,485 schedules built by inserting the new card into an existing sorting run and 9,454 separately generated schedules. Shared-layout and flexible search checks settled the other 660. Complete insertion audit (`published/hard19-extensions/audit.txt` in `regeneration-src.tar.gz`) · Generation and verification (`extend_hard19.py` in `regeneration-src.tar.gz`)

```sh
python verify/audit_hard19_extensions.py coverage/results/n19-ordered/closures verify/published/hard19-extensions
```

Finite 20-card searches vary the source prefix, the prefix of its sorting dual and all compatible remaining cards. The allowed orders come from deletions of the published 21-card and 22-card obstructions. The search report defines the families and records the current completed checks and exact overlaps. Results, archived certificates, and reproduction commands (`published/targeted-families.md` in `regeneration-src.tar.gz`)

```sh
python verify/audit_targeted.py
python verify/terminal_extensions.py
```

A separate finite search selected 13,437 bond-free representatives by extending 280 flexible-cut parents from the main 19-card enumeration. All 13,437 schedules and their duals replay successfully. Selection, counts and reproduction (`published/flexible-lifts.md` in `regeneration-src.tar.gz`)

```sh
python verify/flexible_lifts.py
```
