# `lean-check`: proof-carrying LRAT verification inside Lean

`qdcheck` is a standalone, Mathlib-free Lean 4 executable that checks SAT refutation proofs (**LRAT certificates**) for every case of Jason Davies' frame split directly inside Lean's verified standard-library LRAT checker (`Std.Tactic.BVDecide.LRAT`).

For each case `cs` in `QueenDomSat.enumCases n k`, running `qdcheck n k CERTDIR` reads the compressed certificate `CERTDIR/<ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>.lrat.zst`, builds the formula `QueenDomSat.caseFormula n k cs` using our Lean encoder (`../lean-sat`), and checks the refutation. Its key architectural feature is **proof-carrying output**: the program can print its success status line *only* by constructing a value of type

```lean
PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)
```

which is the exact hypothesis required by the kernel-checked theorem in `../Queens48`:

```lean
(∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) → gamma 48 = 25
```

`qdcheck` reads only the certificate directory; it never touches `enc.py`, `geom.py`, or the SAT run logs. The package is `QueenDomCheck` on Lean 4.36.0 (`lean-toolchain`), depending only on the Mathlib-free encoder package `../lean-sat` (`QueenDomSat`).

## Recorded result for $(n, k) = (48, 24)$

Executed on 2026-11-24 over all **47,580** certificates in `runs/d_48_24.jsonl.lrat` (25 GB compressed, 148.5 GB uncompressed LRAT text) using 5 threads on a busy machine (first directory-path line omitted; command shown relative to checkout):

```text
$ lean-check/.lake/build/bin/qdcheck 48 24 runs/d_48_24.jsonl.lrat --jobs 5 --log data/frame/lean_check_48_24.jsonl
c case list: QueenDomSat.enumCases 48 24, 47580 cases
c result: cases=47580 verified=47580 failed=0 zstd_warnings=0
c proofs: lrat_bytes=148456520357 zst_bytes=24964196706 lemmas=122429776 hints=10891488639 base_formulas_built=55
c time: wall_s=809.860 worker_cpu_s=2778.953 process_cpu_s=2807.000 decompress_cpu_s=431.280 peak_rss_kb=390372
s ALL VERIFIED n=48 k=24 cases=47580
```

- **Outcome:** Exit code `0`, with 47,580 of 47,580 cases verified and 0 failed.
- **Performance:** Wall time 810 s; total CPU time 3,238 s (54 min) across `qdcheck` and its child processes (2,807 s in the checker process and 431 s in decompression); peak memory 390 MB across all 5 threads.
- **Hardest and easiest cases:** The largest case is `(0,1,0,1,0,0,0,0)` (2.25 GB of LRAT text, 2,390,553 lemmas, 75 s of CPU). At the other extreme, unit propagation alone refutes 22,753 cases (their proof is simply the empty clause with hints).
- **Recorded artifacts:**
  - `data/frame/lean_check_48_24.jsonl`: one JSON line per case plus the final summary.
  - `data/frame/lean_check_48_24.summary.json`: totals, final status line, and SHA-256 hashes of the binary (`4388f9e49d7cfbf4168eb0ad7cb5193c8ffec6b808c223b8ca9307b2ba7656cb`) and of all Lean sources in `lean-check` and `lean-sat`. Rebuilding from a fresh source checkout reproduces this binary bit for bit.
  - `data/frame/lean_check_48_24.stdout.txt`: captured stdout.
- **Cross-check (not required for the theorem):** The case list in the log matches `runs/d_48_24.jsonl` exactly, and every case reads the exact `lrat_bytes` recorded there.
- **Reproducibility across earlier builds:** Four earlier runs on the same day used two earlier versions differing only in text formatting and the internal server exit code (`Main.lean`, one line of `Verify.lean`, and `oneLineStr` in `Decompress.lean`):
  - binary `1ca0e023928ed2a520e888808de31ac60d8f7ed00ad0c4a5f152db1ab8b4996d`: 616 s (5 threads), 779 s (6 threads), and 1,378 s (2 threads);
  - binary `8daa81085f4b5dc1cb3bd2950e019f2e2b72b32457aba43c1ec8c9324642f377`: 744 s (5 threads).

  All five runs printed `s ALL VERIFIED n=48 k=24 cases=47580` with exit code `0`, and their per-case logs match on every case in verdict, clauses, lemmas, hints, steps, and bytes.

## Program limits (robustness, not soundness)

- **Adversarial resource limits:** `qdcheck` is not hardened against deliberately adversarial certificates crafted to waste CPU or RAM: a numeral with several hundred thousand digits takes minutes to lex (quadratic in digit count), and a lemma ID near $2^{27}$ inflates the clause-renumbering table to 1 GB or more (~2 GB peak observed). Neither issue can ever cause a false success line, and the actual SAT certificates contain nothing like this.
- **Trailing data and unknown deletions:** Content after the first derived empty clause is ignored, and deletion hints targeting an unknown clause ID are skipped.
- **Checking against `debug.skipKernelTC`:** `#print axioms` (`QueenDomCheck/Axioms.lean`) would not detect a declaration checked under `set_option debug.skipKernelTC`. Neither `lean-sat` nor `lean-check` contains any `set_option`. To verify this mechanically, replay the compiled modules directly through Lean's kernel:
  - In `../lean-sat`:
    ```sh
    lake env leanchecker QueenDomSat.Encode QueenDomSat.Cases QueenDomSat.Formula QueenDomSat.Lemmas
    ```
  - In `lean-check/`:
    ```sh
    lake env leanchecker QueenDomCheck.Stream QueenDomCheck.Formula QueenDomCheck.Combine QueenDomCheck.Verify QueenDomCheck.Lrat QueenDomCheck.Decompress QueenDomCheck.Axioms Main
    ```

## Files and Lean API

| File | Content | Role |
| --- | --- | --- |
| `QueenDomCheck/Stream.lean` | `Verified cnf` (checker state paired with a proof that refuting it refutes `cnf`), `Verified.step`, `Verified.runFrom` (runs the `LRAT.check` loop one step at a time using Std's step functions and lemmas), `checkChunks_sound` | proof-carrying |
| `QueenDomCheck/Formula.lean` | `BaseCNF` (converted base formula for one deficit vector, with proof that it equals `toCNF (mkBase ..).cls`), `prepare`, `caseFormula_eq` (`caseFormula n k cs = base ++ toCNF (extra clauses)`) | proof-carrying |
| `QueenDomCheck/Combine.lean` | `covers`, `forall_of_covers`, `combine` (combines per-case proofs into `∀ cs ∈ l, ..`) | proof-carrying |
| `QueenDomCheck/Verify.lean` | `checkStream`, `verifyCase`, `verifyList`, `verifyAll`; worker threads and logging | glue (`IO`) |
| `QueenDomCheck/Lrat.lean` | Converts LRAT text into gapless `IntAction`s (lexer and clause-ID renumbering) | untrusted |
| `QueenDomCheck/Decompress.lean` | Runs `zstd -dc`, either directly or via a decompression server process | untrusted |
| `QueenDomCheck/Axioms.lean` | `#print axioms` under `#guard_msgs` (build fails if axioms change) | check |
| `Main.lean` | The `qdcheck` executable | glue |
| `scripts/tests.py` | Test suite (positive tests, negative tests, prototype agreement) | tests |
| `scripts/run_check.py` | Runs `qdcheck` and writes the summary JSON with SHA-256 hashes of binary and sources | runner |

Public Lean interface (in `namespace QueenDomCheck`):

```lean
def verifyCase (n k : Nat) (cs : CaseT) (b : BaseCNF n k) (hb : b.Matches cs) (proof : IO ByteArray) :
    IO (Verdict (caseFormula n k cs).Unsat × CaseInfo)
def verifyCase' (n k : Nat) (cs : CaseT) (proof : IO ByteArray) :
    IO (Option (PLift (caseFormula n k cs).Unsat) × CaseInfo)
def verifyList (n k : Nat) (l : List CaseT) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
    IO (Report × Option (PLift (∀ cs ∈ l, (caseFormula n k cs).Unsat)))
def verifyAll (n k : Nat) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
    IO (Except String (PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)))
```

Here `proof` returns the next chunk of LRAT text (or an empty array at EOF), and `Verdict p` is `verified (h : p) | failed (reason : String)`.

## How a success value is constructed

1. **Enumerate cases:** `enumCases n k` builds the full case list (47,580 cases for `(48, 24)`).
2. **Parallel per-case verification:** `jobs` worker threads (dedicated tasks inside one process) pull cases from a shared counter. For each case `cs`, a worker:
   - Fetches the cached base formula for `cs`'s deficit vector. `BaseCNF.build` converts the clauses of `enc.Base` (roughly 130,000 to 240,000 clauses for `(48, 24)`, depending on the deficit vector) once per deficit vector per thread (11 deficit vectors for `(48, 24)`, handed out in groups) and keeps the proof `cnf = toCNF (mkBase n k dR dC dT dS).cls`.
   - Calls `prepare` to append the frame-dependent extra clauses; `caseFormula_eq` (from `QueenDomSat.caseCNF_eq`) proves the resulting CNF equals `caseFormula n k cs`.
   - Runs `checkStream` to stream the decompressed certificate chunk by chunk. The untrusted normalizer turns LRAT text into `IntAction`s, and `Verified.runFrom` feeds them to Std's verified `State.checkRup`, `checkRat`, `checkEmpty`, `add`, and `deleteMany`. The checker state preserves the invariant that refuting the current clause database refutes the original formula, via Std's soundness lemmas (`entails_clause_of_checkRup`, `unsat_of_unsat_of_checkRat`, `entails_deleteMany`, `entails_clause_empty_of_checkEmpty`, etc.). Once the empty clause is verified, the worker holds a proof of `(caseFormula n k cs).Unsat` (`Prepared.unsat` transports it across the formula equality).
   - Returns `(index, ⟨cs, proof⟩ : {cs // (caseFormula n k cs).Unsat})`.
3. **Global assembly:** The main thread places each result into its slot in an array aligned with `enumCases n k`. `covers` verifies that slot `i` holds a verified proof for the `i`-th case in the list, and `forall_of_covers` lifts that check into `∀ cs ∈ enumCases n k, (caseFormula n k cs).Unsat`.
4. **Tamper-resistant status line:** `Main.lean` prints `s ALL VERIFIED n=<n> k=<k> cases=<N>` and exits with code `0` *only* in the `.ok` branch of matching on that proof value. Every other stdout line is prefixed with `c ` via `comment` and `oneLineStr` (which replaces control characters with `?`), preventing external strings (paths, OS errors, or `zstd` error messages) from forging a status line (see test (f)).

*Note on proof erasure:* Because Lean erases proof terms at run time, "holding a proof" means Lean's kernel type-checked the program at build time, guaranteeing that the branch printing `s ALL VERIFIED` can only execute when every runtime check (`checkRup .. = true`, `covers .. = true`, etc.) returned `true`.

## Trust boundary: what is trusted and what is not

### Trusted

- **Lean's kernel and statement definitions:** The kernel checked every definition and proof in `lean-check`, `lean-sat`, and `Std` at build time, including `QueenDomSat.enumCases`, `QueenDomSat.caseFormula` (unfolding to `mkBase`, `caseExtra`, `toCNF`, etc.), and `Std.Sat.CNF.Unsat`.
- **Std's LRAT checker:** `Std.Tactic.BVDecide.LRAT.Internal.State.{ofCNF, checkRup, checkRat, checkEmpty, add, deleteMany}` and their soundness lemmas, used unmodified; our streaming driver in `Stream.lean` is proved from the exact same public lemmas as Std's own `LRAT.check_sound` (`checkChunks_sound`).
- **Compiler, runtime, OS, and hardware:** We trust that compiled code matches its Lean definitions (encoder, case list, checker, and glue in `Verify.lean`, `Combine.lean`, `Formula.lean`), including runtime primitives for arrays, natural numbers, hash maps, threads, reference counting, and the `implemented_by`/`extern` replacements inside Lean core and Std (such as `Array.map` and clause iteration in `Std.Sat.CNF.Clause`). This matches the trust model of any `native_decide`-free Lean executable.
  - None of `native_decide`, `sorry`, `axiom`, `unsafe`, `implemented_by`, `extern`, or `opaque` appear in this package's code (only in comments).
  - Three loops in the untrusted lexer use `partial def`, and `while`/`repeat` loops appear in the lexer and `IO` code, including `checkStream`. Lean's kernel type-checks the loop body of `checkStream` (returning `verified h` requires `h : cnf.Unsat`); trusting that the compiled loop faithfully runs that body is part of trusting the compiler.
- **Standard axioms only:** `propext`, `Classical.choice`, and `Quot.sound` (enforced by `QueenDomCheck/Axioms.lean`; the build fails if any other axiom appears).

### Not trusted

Bugs in any of these components can cause a valid proof to be *rejected*, never an invalid proof to be *accepted*:
- The LRAT certificates themselves, CaDiCaL, `drat-trim`, `enc.py`, `geom.py`, and the SAT run logs.
- Decompression (`zstd`, decompression server processes, and framing between servers and checker).
- The LRAT lexer and clause-ID renumbering (`Lrat.lean`): `drat-trim` numbers lemmas by their index in the untrimmed proof while Std expects consecutive IDs `m+1, m+2, ...`, and a 0-byte LRAT file for a formula that already contains the empty clause is completed with the single missing empty-clause step.
- Thread scheduling, base-formula caching, and array slot assignment (checked at the end by `covers`).
- Logging, statistics, timing, and the summary script.

### Not covered in this package

- That `caseFormula` is satisfiable whenever a dominating set falls into a case (Layer 2, proved in `../Queens48`).
- That the Lean encoder agrees with Python's `enc.py` (unnecessary for soundness; it only explains why Python-generated certificates verify, and `lean-sat/scripts/compare_enc.py` confirms byte-for-byte agreement).

## Build, run, and test

```sh
lake build                                   # in this directory; builds ../lean-sat if needed
.lake/build/bin/qdcheck 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 --log LOG.jsonl
python3 -I scripts/run_check.py 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 \
    --log ../data/frame/lean_check_48_24.jsonl --summary ../data/frame/lean_check_48_24.summary.json \
    --out ../data/frame/lean_check_48_24.stdout.txt
python3 -I scripts/tests.py WORKDIR [--proto PATH/lratcheck]

qdcheck n k CERTDIR [--jobs N] [--log FILE] [--limit M | --cases FILE]
                    [--chunk-mib N] [--zstd CMD] [--direct-zstd] [--progress N]
```

### Runtime notes

- **Dependency:** Requires `zstd` on `PATH` (invoked as `zstd -dc -- FILE`).
- **Output and exit codes:** Stdout consists of `c ...` comment lines followed by a single final status line (`s ...`); verify both the exit code and the status line (as `scripts/run_check.py` does). Passing `--version` anywhere prints the version and exits `0` without a status line. The internal `--decompress-server` flag streams decompressed bytes to stdout and never exits `0`. For an empty case list (such as `(48, 23)`, where no case is admissible), `qdcheck` reads no certificates and prints `s ALL VERIFIED n=48 k=23 cases=0`, which is why the status line always reports the case count.
  - `0`: `s ALL VERIFIED n=.. k=.. cases=..` (entire case list; never returned with `--limit` or `--cases`).
  - `1`: `s NOT VERIFIED ...` (every case is still attempted; failures and reasons go to stderr, the log, and the first 200 to stdout).
  - `2`: usage error.
  - `3`: `s SUBSET VERIFIED ...` (all selected cases via `--limit M` for the first `M` cases, or `--cases FILE` with 8 integers per line, passed; never certifies the full case list even if the subset equals it).
- **JSONL log format (`--log FILE`):** Writes one JSON object per case (`case`, `verdict` = `verified`/`failed`, `reason`, `clauses`, `lemmas`, `hints`, `steps`, `bytes` of LRAT text read, `zst_bytes`, `zstd_rc`, `cpu_ms` of the worker thread, `wall_ms`, `base_cpu_ms` if a base formula was built, and `worker`), followed by `{"summary": {...}}`, whose `all_verified` field is `true` only in the `s ALL VERIFIED` branch.
- **Decompression server:** By default, each worker communicates with a helper process (`qdcheck --decompress-server`, launched before spawning worker threads) that runs `zstd -dc` per certificate and frames the byte stream. Forking directly from a multi-threaded checker costs more than verifying a small certificate; `--direct-zstd` spawns `zstd` directly and was slower in every benchmark.
- **Memory footprint:** Each thread holds the cached base formula for its current deficit vector (~30 MB for $n = 48$), the active proof's live clauses, and one 4 MiB read buffer.

## Test suite (`scripts/tests.py`: 61 checks, 65 with `--proto`)

- **(a) Complete unsatisfiable instance `(n, k) = (8, 4)` (where $\gamma(Q_8) = 5$):** `code/frame/run_cases48.py 8 4` generates all 195 certificates on the spot using CaDiCaL, `drat-trim`, and `zstd`. `qdcheck 8 4` outputs `s ALL VERIFIED n=8 k=4 cases=195` with exit code `0` across 1 to 5 threads, chunk sizes of 1, 5, 7, and 4096 bytes, and both decompression modes. `--limit` and `--cases` always exit `3` and never print `s ALL VERIFIED`.
- **(b) Satisfiable instance `(6, 3)`:** 1 of the 98 cases is satisfiable and lacks a certificate. `qdcheck` exits `1` without a success line, even if that missing certificate is replaced by any of the other 97.
- **(c) Negative tests on `(8, 4)`:** Missing, empty, damaged, or truncated certificates; proofs omitting the empty clause or missing/incomplete hints; removed lemmas; removed or reversed hints; garbage bytes; and certificates swapped from other cases (single swap, pairwise swap, or full rotation). Every single test exits `1` with `s NOT VERIFIED`, while valid cases still pass.
- **(e) Formulas already containing the empty clause:** For non-admissible cases where `drat-trim` emits a 0-byte LRAT file, `qdcheck` verifies them via the added final step, while rejecting the same 0-byte file for any formula without an empty clause. Unit-propagation refutations (a deletion line plus the empty clause) account for 133 of 195 cases in `(8, 4)` and roughly half of `(48, 24)`.
- **(f) Status-line forgery resistance:** A certificate directory or `--cases` path containing a newline followed by `s ALL VERIFIED ...`, or a decompressor printing that string to stderr and failing, still exits `1` with exactly one `s ` line (`s NOT VERIFIED`), all other stdout lines prefixed by `c `, and no forged line on stderr. The internal decompression server exits `4` and rejects `n k CERTDIR`, and an empty case list reports `cases=0`.
- **(d) Prototype comparison (only with `--proto`):** Because the earlier standalone prototype is not in this repository, these 4 checks cannot be run from this repo alone. Where available, they compare against `lratcheck --stream` (parsing DIMACS from `enc.py`) across 67 cases of `(48, 24)` spanning all 11 deficit vectors, confirming identical verdicts, lemma and hint counts, and byte counts, plus mutual rejection on 14 swapped certificates.
