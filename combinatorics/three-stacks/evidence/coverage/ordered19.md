# Auditing and reproducing the length-19 ordered search

The completed computation proves that every 19-card permutation sorts with three stacks in series. The archive audit covered all 5,040 suffix groups and all 6,402,373,705,728,000 orderings ending in 1. It reconciled 26,409,361 individually recorded candidates and replayed the full 76-move sorting schedules for the 384 that needed the final test. The swap argument extends the conclusion to every possible final card. Completed audit (`results/n19-audit.json` in `results.tar.gz`) · [End-card reduction](README.md)

## Domain and ownership

After the final-1 reduction, each of the 5,040 relative orders of the seven positive cards after position 11 contributes $11!\binom{18}{7}=1{,}270{,}312{,}243{,}200$ decks. Together these domains contain $18!$ decks. A descending adjacent pair of consecutive labels permits a contraction to the verified length-18 problem. The sorting dual is the involution $D(p)_{18-p_i}=18-i$ in zero-based coordinates. [Reduction and length-18 proof](README.md) · [Sorting-dual proof](../verify/README.md)

The recorded priority fixes 4,140 suffix orders for a full scan. Their workers test both lexicographic orientations when appropriate. For the 900 remaining suffix orders, let $t$ be the order of the input suffix and $d$ the order of the dual suffix. If $t\ne d$, the worker with earlier priority owns the orbit. If $t=d$, the worker owns the lexicographically smaller member including equality. Thus an orbit containing an input with a full-scan suffix is covered, and every orbit of two grouped suffixes has a representative.

For a fixed suffix order and numerical suffix set, let $b$ be the number of labels from $1,\ldots,7$ occurring in the prefix in zero-based coordinates. These labels supply the $b$ smallest standardized prefix letters. Reading the positions of original labels $7,6,\ldots,1$ in reverse coordinates gives the dual suffix. Its relative order depends only on the original suffix order, the subset of these seven labels in the suffix, and the order of the other $b$ labels in the prefix. Each such prefix class contains $11!/b!$ heads. The independent checker enumerates all 12,109,152 nonempty grouped classes and counts all numerical suffix sets satisfying the tail bond test. Across the full domain it predicts 5,359,230,399,790,080 tuples owned by the scans. The independent low-index checker reconstructs the physical low subword of every eleven-letter head and checks all 239,500,800 stored index entries. Ordered join (`ordered_join.cpp` in `regeneration-src.tar.gz`) · [Independent ownership enumeration](check_ordered_ownership.cpp) · Expected domain counts (`results/n19-ordered-domains.csv.gz` in `results.tar.gz`) · Low-index check (`check_low_index.cpp` in `regeneration-src.tar.gz`)

## Live and preserved audits

Run these commands from the project root. The final command requires the completed archive.

```sh
work=/var/tmp/deck-series-cam
python coverage/audit19.py --live "$work/19-ordered.tsv" "$work/19-ordered-closed" --partial
python coverage/audit19.py --live "$work/19-ordered.tsv" "$work/19-ordered-closed" \
  --save coverage/results/n19-ordered
python coverage/audit19.py coverage/results/n19-ordered
```

The live audit checks the exact sequence of completed suffix ranks against each worker's assigned list. It compares the independently predicted ownership count at each rank with the primary log. The `bulk` category counts owned inputs settled before an individual leaf. The leaf log records direct or dual certificates, contractions or symmetry decisions, and pending inputs. It reports a combined count for the nested cuts at 9 and 8 through the difference between the leaf total and its other categories.

Every completed closure must agree with the primary `pending` count **for each rank**. Six recuts, the flexible cuts and the final literal sorting words must conserve the closure's input count. The audit also checks ordinal continuity of each batch and unique closure ownership. It verifies the card labels, rank, symmetry assignment and all 76 stack moves for every individual witness. A complete result must account for exactly $18!$ representatives. [Stage checker and replay](audit19.py) · Closure implementation (`close_ranges.py` in `regeneration-src.tar.gz`) · [Physical stack interpreter](../verify/replay.py)

The `--save` command requires every rank and every closure to be present. It freshly compiles the independent ownership enumerator and checks every predicted per-rank domain against its output. It rereads the entire raw stream of each worker and checks deck uniqueness within each rank, physical labels, bond status, suffix assignment, symmetry ownership and the membership of all final individual inputs in that stream. It records SHA-256, byte and row counts, then atomically publishes a new directory containing the original rank lists, progress logs, closure manifests, residual inputs and sorting words. It refuses to overwrite an existing archive. Pass `--stream-checker /absolute/path/to/binary` to use a previously compiled raw validator. The default compiles the checker into a temporary directory. [Raw-stream checker](check_ordered_stream.cpp)

For a self-contained archive of every raw candidate, add `--include-raw` to `--save`. A later archive audit with `--stream-checker` will check all those raw candidate decks again. A compact archive retains their digests and the verified raw counts. Regular archived audits check the immutable-file manifest, all accounting, and the embedded literal sorting words. Add `--recompute-ownership` to repeat the independent numerical enumeration of the domains from the saved priority.

## Fresh reproduction

The build uses a C++20 compiler on Linux. Generating fresh SAT witnesses requires the Python package `python-sat` with CaDiCaL 1.9.5 support. The original witness environment used `python-sat==1.9.dev25`. The completed archive supplies the seven worker rank lists and historical closure-batch boundaries. Use a fresh work directory with room for the 7.7 GB raw continuation table, at least 7 GB of other tables and indices, and the raw candidate streams. Start with one or two primary workers where memory is limited. Bounded-search budgets determine how many cases reach later stages. [SAT witness environment](../verify/README.md)

```sh
python -m venv /tmp/three-stack-python
/tmp/three-stack-python/bin/python -m pip install 'python-sat==1.9.dev25'
PYTHON=/tmp/three-stack-python/bin/python coverage/reproduce19.sh /var/tmp/reproduce-stacks19 --workers 2
python coverage/audit19.py /var/tmp/reproduce-stacks19/proof
```

The phases `build`, `tables`, `primary`, `close`, and `archive` may be invoked separately, in that order, by adding the phase after the work directory. The primary phase uses exclusive opens for its output files. The tables phase builds the cut-8 through cut-11 prefix masks, the budget-1,800 cut-11 continuation table, its lossless dictionary, the prefix index and the low-order index. It independently verifies every packed continuation row, every low-index membership and every grouped ownership domain. The close phase uses the recorded batches, verifies their per-rank counts and compares the fresh recut counts and residual decks with the originals. The archive phase compares every raw-stream digest and primary counter with the preserved run, excluding elapsed time. To run against a live external schedule, pass `--schedule /path/to/worker-manifest.tsv` to the build and close phases, or once to the combined command. Fresh grouping of closures can change later bounded-search stage counts. Reproduction driver (`reproduce19.py` in `regeneration-src.tar.gz`)

The primary workers switched to a smaller exact dual lookup at the suffix boundaries listed in the restart file (`results/n19-primary-restarts.json` in `results.tar.gz`). Both versions compute the full normalized prefix and suffix addresses. The faster version precomputes two factorial codes for each normalized head and stores 16 selected layout bits at each prefix and suffix address. Any shared bit certifies the same actual stack configuration. A miss proceeds to the original full comparison. The checker (`verify/check_ordered_projection.cpp` in `regeneration-src.tar.gz`) separately rebuilt all 39,916,800 prefix codes and projected masks and all 160,392,960 projected suffix rows. Observed check (`results/n19-projected-check.txt` in `results.tar.gz`) · Projection builder (`project_ordered_tables.cpp` in `regeneration-src.tar.gz`)

A further physical check sampled 30,000 length-19 decks, computing their table addresses directly from their card values. For 29,993 of them the two masks intersected. For each such input the checker picked one of the shared configurations, reconstructed both halves using individual stack operations, and replayed the full 76-move schedule from the original input. Independent word reconstruction (`verify/audit19_join_words.cpp` in `regeneration-src.tar.gz`) · Results (`results/n19-physical-join.txt` in `results.tar.gz`)
