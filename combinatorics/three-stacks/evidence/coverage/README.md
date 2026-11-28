# Exhaustive coverage of three-stack sorting

Every permutation through length 19 can be sorted by three stacks in series. The length-19 computation uses a cut after eleven cards and has its own proof and reproduction instructions. The earlier computations below use a cut after ten cards and establish the induction used at length 19. All cards are listed in arrival order. A transfer moves one card one step to the right. [Length-19 proof](ordered19.md) · Completed audit (`results/n19-audit.json` in `results.tar.gz`)

## Why ending in 1 suffices

Let the input end in $x$, and form a second input by swapping $x$ with 1. Suppose the second input has a sorting run. Erase the operations on 1 and $x$ from that run. When the run would first read $x$, send the original input's 1 through the three stacks to the output. When the run would output $x$, read the original input's final $x$ and send it through to the output. All other cards have already been read at this point, since the run has output its own last-read 1. The other cards follow their original operations. Thus sorting every deck ending in 1 suffices. This argument works for any number of stacks.

## What the tables certify

Use zero-based labels in the code, so the last card is 0. Cut an input immediately after the tenth card is read. Consider configurations with at most two cards in stacks one and two combined. Every other prefix card is in stack three in decreasing order from bottom to top. Each configuration specifies which relative prefix ranks are retained in each of the first two stacks, in bottom-to-top order. There are 291 configurations, comprising one empty choice, 20 singleton choices and 270 ordered two-card choices.

For each of the $10!$ prefix orders the first table gives a 291-bit mask. A set bit certifies a sequence of transfers that reads the prefix and reaches that configuration without output. During this search, an entry assigned to stay in the first or second stack can be treated as a permanent floor once placed. The other entries must arrive at stack three in decreasing order. This is implemented in the prefix layout test (`knuth/layout.hpp` in `regeneration-src.tar.gz`).

For each possible remaining input and prefix value set, the second table gives a mask over the same configurations. A set bit certifies a continuation that empties all stacks in increasing order. One test uses the first two stacks to sort the active cards, merging them with the sorted contents of the third. A second test tries physical three-stack moves. Both tests only accept upon reaching the sorted output. The physical search has a node budget. An unmarked bit leaves the configuration available for other verification methods. Two-stack continuations (`tail.hpp` in `regeneration-src.tar.gz`) · Three-stack continuations (`gaps.hpp` in `regeneration-src.tar.gz`) · Physical move search (`structural/reach.hpp` in `regeneration-src.tar.gz`)

The physical search merges each consecutive run of initial stack-three cards between neighboring active values into one marker. These runs are already in the required pop order. To expand a successful run, replace the pop of the marker by pops of the entire run. Initial cards larger than every active card can be left at the bottom and popped at the end. Consequently the tail computation can reuse a result for every placement with the same occupied gaps.

**If the two masks share a set bit, concatenate the certified prefix and suffix runs.** The same *relative* configuration determines the same physical cards and stack orders because the prefix value set is fixed. This is how the calculation certifies many complete inputs together.

Two additional reductions apply to a missed input.

- The sorting dual sends a point $(i,p_i)$ in zero-based notation to $(n-1-p_i,n-1-i)$. Reversing time and the order of the stacks, and relabeling the cards, transfers a sorting run between the two permutations. The dual also ends in 0. [Vatter, Proposition 5.2](https://arxiv.org/html/2602.16355v4)
- For length 17, an adjacent descending pair of consecutive values can be contracted. Sort the resulting 16-card deck, replacing each move of the contracted card by two moves. The pair stays together and reverses orientation once per stack, hence reaches the output in increasing order. The length-16 run uses no contraction assumption.

## Full counts

| Length | Inputs ending in 1 | Shared configuration | Descending-pair reduction | Shared configuration for the dual | Individually replayed |
|---|---:|---:|---:|---:|---:|
| 16 | 1,307,674,368,000 | 1,307,674,221,980 | 0 | 146,020 | 0 |
| 17 | 20,922,789,888,000 | 20,922,726,210,985 | 9,199,295 | 54,459,680 | 18,040 |

At length 17 the $6!$ orders of the six unread positive cards, the $\binom{16}{6}$ ways to choose them, and the $10!$ prefix orders give exactly $16!$ inputs. The 18,040 individual proofs are 68-move sorting schedules. The digits 1 to 4 stand for input to stack one, stack one to two, stack two to three, and stack three to output.

The join indexes exact masks. It may group ranks that share a mask, skip a block when every rank in it shares a successful bit, or use a subset of mask positions to rule out a shared bit in selected groups. It examines the full masks of the remaining candidates. An independent program groups suffix masks by inclusion and reproduced the same 18,040 residual inputs. Join (`join.cpp` in `regeneration-src.tar.gz`) · Independent join (`verify/join_audit.cpp` in `regeneration-src.tar.gz`) · Move-level checks (`verify/layout_audit.cpp` in `regeneration-src.tar.gz`) · Gap checks (`check_tail.cpp` in `regeneration-src.tar.gz`)

## The length-18 computation

The length-18 run covers all $17!=355{,}687{,}428{,}096{,}000$ inputs ending in 1. It again cuts after ten cards. There are $7!$ relative orders for the remaining positive cards and $\binom{17}{7}=19{,}448$ possible sets of their labels. The length-17 result justifies contracting descending adjacent pairs.

| Reason a deck sorts | Number of inputs |
|---|---:|
| Shared configuration at the ten-card cut | 355,676,106,006,155 |
| Descending-pair contraction | 2,176,260,121 |
| Shared configuration for its sorting dual | 7,025,048,793 |
| Represented by its lexicographically smaller sorting dual | 2,095,442,870 |
| Another shared configuration at an eight- or nine-card cut | 25,324,776 |
| Individual 72-move sorting schedule | 13,285 |
| **Total** | **355,687,428,096,000** |

Four search partitions use the projection index. Two use the independent inclusion-based join and process one representative when a pair of duals can reach this reduction. The larger member of such a pair inherits the verdict of the smaller member; every smaller member is in the enumerated universe. For the remaining inputs, the calculation checks cuts after nine and eight cards, then the same cuts for the dual. The checks use the same prefix preparation and continuation rules. The six partition ranges, counts, and final sorting words are stored in the results directory. The audit checks that the ranges partition all 5,040 suffix ranks, checks each count, and replays every final schedule. [Audit](audit18.py) · Additional cut checks (`recut.cpp` in `regeneration-src.tar.gz`) · Recorded audit (`results/n18-audit.txt` in `results.tar.gz`)

Run the saved audit from the workspace root with standard Python.

```sh
python coverage/audit18.py
```

The full reproduction script (`reproduce18.sh` in `regeneration-src.tar.gz`) rebuilds both tables and reruns the length-18 partitions. It takes a working-directory argument for the binary tables and intermediate output.

## Reproduce the length-17 bound

From the workspace root, build the prefix table once. It occupies about 145 MB. The length-17 suffix table occupies about 231 MB.

```sh
work=$(mktemp -d)
g++ -O3 -march=native -std=c++20 coverage/build_prefix.cpp -o "$work/prefix"
"$work/prefix" "$work/prefix.bin"
for n in 16 17; do
    g++ -O3 -march=native -std=c++20 -DDECK_SIZE=$n coverage/build_tail.cpp -o "$work/tail"
    g++ -O3 -march=native -std=c++20 -DDECK_SIZE=$n coverage/join.cpp -o "$work/join"
    "$work/tail" "$work/tail$n.bin" 2400
    "$work/join" "$work/prefix.bin" "$work/tail$n.bin" > "$work/remaining$n.txt"
done
```

The saved words can be replayed with standard Python, without installing a SAT solver.

```sh
python coverage/replay.py "$work/remaining17.txt" coverage/results/n17-words.txt.gz
```

To generate fresh sorting words, install `python-sat` in a Python environment and run the following command.

```sh
python coverage/settle.py 17 "$work/remaining17.txt" "$work/new-words.txt.gz"
```

The SHA-256 values from the little-endian x86-64 run are `d76cc161a4220146434773e34daf6056bb77cfe8567bcd7311fc2aa7522a0c33` for the prefix table and `73a095390d9fd061bceb8d06d19e930582e98c78af52ce261f7b11447169397c` for the length-17 suffix table.
