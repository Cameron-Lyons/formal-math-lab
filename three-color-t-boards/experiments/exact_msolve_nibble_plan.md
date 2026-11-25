# Checked nibble storage: concrete plan, no ninth executable

This pass stops at a source-pinned implementation plan. No solver source,
predecessor build, or executable was changed, and no solver was run. The
representation is feasible in principle, but it is not a safe local typedef
or allocation-size patch. Direct dense-vector access is spread across hash
arithmetic, comparison, input/output, cached pointers and final reduction.
A missed access can silently change a monomial, order or divisor test while
still producing a completed basis. Those sites need an explicit vector API
conversion before the packed representation can be accepted.

The baseline is frozen eighth executable SHA-256
`63e52125aba520101ccc7f4f188c626824cf867ebbd80390fbd03ec8c606da76`,
from pinned msolve commit `cc044551f8e202d00691990fd3fd0b1226a88ea2`.
`exact_msolve_nibble_plan.py/.json` pins the relevant source files and lists
matching line references. The inventory is a static aid, not a claim of
complete call-graph verification.

## Proposed representation and exactness boundary

Keep logical exponent/degree arithmetic in checked bytes, exactly as in
build eight. Keep short stack multipliers and input scratch vectors dense.
Pack only persistent table vectors, with byte zero containing the full
checked degree and the following bytes containing two variable coordinates
each. Logical `evl=n+1` stays unchanged; physical `vector_bytes=1+ceil(n/2)`
is a separate checked field. The random hash coefficients and divisor-map
indices stay indexed by logical coordinates.

Introduce distinct dense-scratch and packed-vector types. Provide only
explicit checked pack/unpack/read operations, plus packed-to-packed copy.
Before packing a candidate, validate the complete dense vector: degree in
[0,255], each coordinate in [0,15], correct degree sum, and expected logical
length. A coordinate of 16 must exit nonzero before any completion marker;
it must never be masked or reduced. The current degree theorem does not
prove that generated coordinates stay at most 15. No such stronger bound
is assumed here. This preserves ordinary polynomial arithmetic and adds a
clearly detected resource/representation limit.

Canonicalize the unused high nibble when the variable count is odd.
Comparisons, divisibility and hash values must read logical coordinates,
not use bytewise order: storing x1 in the low nibble would make raw byte
order incompatible with DRL. Preserve the original logical hash sum and
ascending insertion order, so successful computations retain the same hash
IDs, pair handling and coefficient row data as build eight.

## Exact source sites requiring conversion

References below are in the frozen eighth source tree under
`exact_msolve_byte_exponent_tools/msolve-cc044.../`.

| Area | Concrete sites | Required distinction |
|---|---|---|
| Layout | `src/neogb/data.h:140`, `:152` | Separate logical lanes, physical stride, packed table pointers and dense scratch type. |
| Initial/copy/secondary tables | `hash.c:111`, `:161`, `:214` | Slab allocations and pointer reconstruction use physical stride; `rn` keeps logical length. |
| Legacy growth and generic reset | `hash.c:332`, `:895`, `:1668` | Growth needs physical stride. Generic reset is currently excluded from this ordinary export route, but must remain layout-correct if compiled as a supported helper. |
| Checked rounded reserve | `hash.c:1080`–`:1145` | Overflow guards must use physical vector bytes while preserving power-of-two bucket invariants. |
| Staging | `hash.c:1250`–`:1360`, `:1476` | Inverse pointer validation, overlap-safe compaction, shrink/reset and staged lookup all use physical stride. |
| Hash/divisor operations | `hash.c:396`, `:423`, `:477`, `:550`, `:648`, `:713`, `:762`, `:820`, `:1587` | All aliased exponent reads become logical accessors; dense candidates and packed stored entries must not share an ambiguous pointer contract. |
| Legacy/full and support-only promotion | `hash.c:978`, `:1040`, `:1375`, `:1512` | Includes final interreduction and unused symbolic columns, not only ordinary retained supports. |
| Multiplied rows and LCM | `hash.c:1548`, `:1739`; `symbol.c:211`, `:318`, `:354`, `:510` | Dense checked scratch reads packed basis/symbolic vectors; pack only through the checked insertion boundary. |
| DRL comparisons | `order.c:408`, `:440`, `:480`, `:512` | Degree reads plus reverse logical-coordinate scans; preserve tie behavior exactly. |
| Input conversion | `io.c:27`, `:302` | Populate dense scratch first, then checked packing; `ht->ev[0]` is currently a packed-table candidate alias and cannot remain the implicit dense scratch. |
| Column conversion | `convert.c:39`, `:528`, `:672` | Zero/scratch handling and degree reads use the new API; preserve ordinary versus final promotion dispatch. |
| Final reduction control | `f4.c:578`; `convert.c:675` | Final reduction still invokes the legacy all-column importer; it needs the same storage checks. |
| Leading export | `msolve/hilbert.c:3858` | `get_lm_from_bs` reads table coordinates before the completion marker. |
| g1/g2 text export | `msolve/iofiles.c:173`–`:319` | Every emitted exponent must be unpacked by logical index. |

The grep inventory also finds `msolve/linear.c`, `lifting-gb.c`, saturation,
signature and trace accessors. These are not all reachable in the allowed
prime/no-trace/export mode. In particular `msolve.c:1685` returns after
export, before `check_and_set_linear_poly` at `:1706`; linear-form extraction
and staircase enumeration are outside the active path. They must nevertheless
either compile against a sound packed-vector API or be excluded explicitly,
with the existing pre-import mode rejection retained. The current ordinary
F3 scope, parser and arithmetic checks must remain at least as restrictive
as build eight. Coefficient linear algebra is unchanged.

The parent/counter's reset audit also confirms that ordinary `core_f4`
never invokes `reset_hash_table`. Its only caller is the excluded
`f4sat_trace_application_test_phase` in `modular.c:459`. The accepted `-u`
option is parsed, stored and printed but does not cause reclamation in the
current route. Reset coverage in the proposed helper tests is generic
layout compatibility, not a claim of active ordinary-run reclamation.

## Safer staged implementation

1. First introduce the dense-versus-stored vector API while retaining byte
   storage. Use distinct types to make accidental dense indexing of stored
   vectors visible to the compiler. Finish the reachable alias/access audit,
   including input scratch slot zero and final interreduction. Demonstrate
   byte-identical completed g1/g2 exports against frozen eight.
2. Change only that API's physical storage implementation and checked
   allocators to nibbles. Keep the arithmetic and monomial/hash semantics
   unchanged. Freeze a separately preserved candidate and exact patch.
3. Run the packing, actual table and basis checks below, then obtain the
   independent reviewer approval before any full-board use.

This staged approach is preferable to replacing `evl` mechanically: its
same value currently controls both logical arithmetic loops and physical
pointer arithmetic, while the `exp_t *` type currently denotes both dense
scratch and stored vectors. A broad textual replacement cannot establish
which meaning an alias has.

Required validation includes odd/even variable counts, canonical padding,
coordinates 0/15 and rejection 16, degree 255 and rejection 256, checked
addition/subtraction before narrowing, and field-domain/parser rejections.
Actual-table tests must cover deliberate hash collisions, divisor masks,
DRL comparisons, LCM/multiplied rows, grow/reset/copy, reused and new entries,
non-power-of-two capacities, in-place staging overlap, restored-secondary
reuse and every allocation-failure branch. ASan+UBSan should run on the
actual helpers. Basis checks must include g1 and g2, unit/zero and mixed
ideals, the known-six prefix, and 127 independent F3 domains with exact
dimension 3^127. Completion errors must be nonzero and marker-free.

## Memory opportunity, not a measured saving

For n=96, stored exponent data would occupy 49 instead of 97 bytes per
vector; n=97 gives 50 instead of 98, and n=93 gives 48 instead of 94.
Metadata, pointer arrays, buckets, sparse row indices and coefficients do
not shrink. Dense scratch uses at most 128 bytes per vector and can remain
unpacked without affecting the main saving.

The JSON report computes hypothetical same-capacity slab savings from the
last logged capacity requests in the two terminal byte-build runs. A
capacity request alone does not prove successful allocation, and a slab
calculation is not a measured peak-memory or runtime improvement. Even a
correct packed representation can still hit other allocations or its
explicit coordinate limit. There is no ninth-build performance or
completion claim in this plan.
