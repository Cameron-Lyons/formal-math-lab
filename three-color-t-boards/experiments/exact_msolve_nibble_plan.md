# Checked nibble storage: concrete plan, no ninth executable

This note stops at a source-pinned implementation plan. No solver source, predecessor build, or executable was edited, and no solver was run. Nibble-packed exponent storage is feasible, but it cannot be implemented safely as a small typedef or allocation-size patch: direct dense-vector indexing is scattered across hash arithmetic, comparisons, I/O, cached pointers, and final reduction. A single missed read could silently corrupt a monomial, term order, or divisibility check while still outputting a completed basis. Those sites need an explicit typed vector API before packing can be trusted.

Baseline: frozen eighth executable SHA-256 `63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76` (from pinned msolve commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`). `exact_msolve_nibble_plan.py` and `.json` pin the source files and list matching line references as a static guide rather than a full call-graph proof.

## Proposed representation and exactness boundary

Keep logical exponent and degree arithmetic in checked bytes, matching build 8, and keep short stack multipliers and input scratch vectors dense. Pack only persistent hash-table vectors: byte 0 stores the full checked total degree, and each following byte packs two variable coordinates (4 bits each). Logical `evl = n + 1` stays unchanged, while physical `vector_bytes = 1 + ceil(n / 2)` becomes a separate checked field. Random hash weights and divisor-map indices stay indexed by logical coordinates.

Use distinct C types for dense scratch and packed table vectors, exposing only checked pack, unpack, read, and packed-copy operations. Before packing any vector, verify that total degree is in `[0, 255]`, every coordinate is in `[0, 15]`, the coordinates sum to the stored degree, and logical length matches. Any coordinate reaching 16 must exit nonzero before writing a completion marker and must never be masked or reduced. Because the current degree proof does not cap generated symbolic coordinates at 15, this design enforces an explicit representation limit while keeping polynomial arithmetic exact.

When `n` is odd, zero the unused high nibble canonically. Comparisons, divisibility checks, and hashing must read logical coordinates rather than comparing raw bytes, because placing `x1` in the low nibble breaks bytewise DRL order. Keeping the exact logical hash sum and ascending insertion order preserves build 8's hash IDs, pair handling, and coefficient rows on every run that stays within the coordinate bound.

## Source sites needing conversion

Line numbers refer to the frozen eighth source tree under `exact_msolve_byte_exponent_tools/msolve-cc044.../`.

| Area | Concrete sites | Required distinction |
| --- | --- | --- |
| Layout | `src/neogb/data.h:140`, `:152` | Separate logical lanes, physical stride, packed table pointers, and dense scratch type. |
| Initial/copy/secondary tables | `hash.c:111`, `:161`, `:214` | Slab allocations and pointer reconstruction use physical stride; `rn` keeps logical length. |
| Legacy growth and generic reset | `hash.c:332`, `:895`, `:1668` | Growth needs physical stride. Generic reset is excluded from the ordinary export path, but must stay layout-correct if compiled. |
| Checked rounded reserve | `hash.c:1080` to `:1145` | Overflow guards must use physical vector bytes while keeping power-of-two bucket invariants. |
| Staging | `hash.c:1250` to `:1360`, `:1476` | Inverse pointer checks, overlap-safe compaction, shrink/reset, and staged lookup all use physical stride. |
| Hash/divisor operations | `hash.c:396`, `:423`, `:477`, `:550`, `:648`, `:713`, `:762`, `:820`, `:1587` | All aliased exponent reads become logical accessors; dense candidates and packed entries cannot share an ambiguous pointer type. |
| Legacy/full and support-only promotion | `hash.c:978`, `:1040`, `:1375`, `:1512` | Covers final interreduction and unused symbolic columns as well as ordinary retained supports. |
| Multiplied rows and LCM | `hash.c:1548`, `:1739`; `symbol.c:211`, `:318`, `:354`, `:510` | Dense checked scratch reads packed basis/symbolic vectors and packs only at the checked insertion boundary. |
| DRL comparisons | `order.c:408`, `:440`, `:480`, `:512` | Degree reads plus reverse logical-coordinate scans with exact tie behavior. |
| Input conversion | `io.c:27`, `:302` | Fill dense scratch first, then pack with checks; `ht->ev[0]` currently aliases a packed slot and cannot stay an implicit dense buffer. |
| Column conversion | `convert.c:39`, `:528`, `:672` | Zero/scratch handling and degree reads use the new API while keeping ordinary vs. final promotion dispatch. |
| Final reduction control | `f4.c:578`; `convert.c:675` | Final reduction still calls the legacy all-column importer and needs the same storage checks. |
| Leading export | `msolve/hilbert.c:3858` | `get_lm_from_bs` reads table coordinates before writing the completion marker. |
| g1/g2 text export | `msolve/iofiles.c:173` to `:319` | Every exported exponent must unpack by logical index. |

The grep inventory also flags `msolve/linear.c`, `lifting-gb.c`, and saturation, signature, and trace accessors. They are unreachable in the allowed prime, no-trace export mode (`msolve.c:1685` returns after export, before `check_and_set_linear_poly` at `:1706`, so linear-form extraction and staircase enumeration never run). Still, those files must either compile against a sound vector API or be excluded explicitly, keeping all build-8 scope, parser, and arithmetic checks intact. Coefficient linear algebra stays unchanged.

The reset audit also confirms that ordinary `core_f4` never calls `reset_hash_table`; its only caller is the excluded `f4sat_trace_application_test_phase` (`modular.c:459`). The `-u` flag is parsed and printed without reclaiming memory in this mode. Reset tests in the plan below check layout compatibility rather than ordinary-run reclamation.

## Staged implementation plan

1. **Introduce the typed vector API while keeping byte storage.** Distinct types let the compiler catch any accidental dense indexing of stored vectors. Finish auditing every reachable alias (including input scratch slot 0 and final interreduction) and verify byte-identical `-g 1` / `-g 2` exports against build 8.
2. **Swap only the physical storage layer and checked allocators to nibbles.** Keep arithmetic, hashing, and monomial semantics identical, and freeze a new candidate build and exact patch.
3. **Run full packing, table, and basis tests, then get independent review** before running any full-board input.

Doing this in two stages avoids the trap of mechanically replacing `evl`: right now `evl` drives both logical loops and physical pointer arithmetic, and `exp_t *` points to both dense scratch and stored vectors. Textual find-and-replace cannot tell which role each pointer plays.

Required validation before acceptance:

- Odd and even variable counts, canonical padding, coordinates 0 and 15 (accepted) vs. 16 (rejected), degree 255 vs. 256, checked add/sub before narrowing, and all field-domain and parser rejections.
- Actual-table ASan+UBSan tests covering forced hash collisions, divisor masks, DRL comparisons, LCMs and multiplied rows, grow/reset/copy, reused and new entries, non-power-of-two capacities, overlapping in-place staging, restored-secondary reuse, and every allocation-failure branch.
- Basis checks covering `-g 1` and `-g 2`, unit/zero/mixed ideals, the six-completion prefix, and 127 independent F3 domains (exact dimension `3^127`), with all errors exiting nonzero and emitting no completion marker.

## Memory estimate

For `n = 96`, packed vectors drop from 97 bytes to 49 bytes (`n = 97`: 50 vs. 98; `n = 93`: 48 vs. 94). Metadata, pointer arrays, buckets, sparse row indices, and coefficients stay the same size. Dense scratch takes at most 128 bytes per vector and can stay unpacked.

`exact_msolve_nibble_plan.json` computes hypothetical same-capacity slab savings from the last logged capacity requests of the two terminal byte-build runs. A logged request does not prove an allocation succeeded, and a slab estimate is not a measured peak-memory or speed gain. Even a correct packed build can hit other allocations or its coordinate limit; this plan makes no performance or completion claims.
