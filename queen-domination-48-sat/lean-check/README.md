# lean-check: checking frame-method certificates inside Lean

For every case `cs` in `QueenDomSat.enumCases n k`, `qdcheck n k CERTDIR` checks the stored LRAT certificate `CERTDIR/<ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>.lrat.zst` against the formula `QueenDomSat.caseFormula n k cs` built by the Lean encoder (`../lean-sat`), using Lean's verified standard-library LRAT checker (`Std.Tactic.BVDecide.LRAT`). The program can only report success by constructing a term of type

```lean
PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)
```

This is the hypothesis of the theorem proved in `../Queens48`:
`(∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) → gamma 48 = 25`.
The checker reads only the certificate directory; it does not read `enc.py`, `geom.py`, or the SAT run logs.

The package is `QueenDomCheck` on Lean 4.36.0 (`lean-toolchain`), with no Mathlib dependency. Its only dependency is the Mathlib-free package `../lean-sat` (`QueenDomSat`, providing the encoder and case list).

## Result for (n, k) = (48, 24)

Run on 2026-11-24 over all 47,580 certificates in `runs/d_48_24.jsonl.lrat` (25 GB compressed, 148.5 GB of LRAT text) using 5 threads on a busy machine. The first output line (the directory path) is omitted, and the command is written relative to the checkout:

```text
$ lean-check/.lake/build/bin/qdcheck 48 24 runs/d_48_24.jsonl.lrat --jobs 5 --log data/frame/lean_check_48_24.jsonl
c case list: QueenDomSat.enumCases 48 24, 47580 cases
c result: cases=47580 verified=47580 failed=0 zstd_warnings=0
c proofs: lrat_bytes=148456520357 zst_bytes=24964196706 lemmas=122429776 hints=10891488639 base_formulas_built=55
c time: wall_s=809.860 worker_cpu_s=2778.953 process_cpu_s=2807.000 decompress_cpu_s=431.280 peak_rss_kb=390372
s ALL VERIFIED n=48 k=24 cases=47580
```

* Exit code 0, with 47,580 of 47,580 cases verified and 0 failed.
* Wall time 810 s and total CPU time 3,238 s (54 min) across `qdcheck` and its child processes: 2,807 s in the checker process and 431 s in decompression. Peak memory was 390 MB across all 5 threads.
* The hardest case is `(0,1,0,1,0,0,0,0)` (2.25 GB of LRAT text, 2,390,553 lemmas, 75 s of CPU). Unit propagation alone refutes 22,753 cases (their proof is just the empty clause with hints).
* Recorded files: `data/frame/lean_check_48_24.jsonl` (one line per case plus the summary), `data/frame/lean_check_48_24.summary.json` (totals, final line, and SHA-256 hashes of the binary `4388f9e49d7cfbf4168eb0ad7cb5193c8ffec6b808c223b8ca9307b2ba7656cb` and of the Lean sources of `lean-check` and `lean-sat`), and `data/frame/lean_check_48_24.stdout.txt`. Building from a fresh copy of the sources reproduces the binary bit for bit.
* Cross-check (not needed for the theorem): the cases in the log match `runs/d_48_24.jsonl` exactly, and every case reads the exact `lrat_bytes` recorded there.
* Earlier runs on the same day used two earlier versions differing only in text formatting and the internal server exit code (`Main.lean`, one line of `Verify.lean`, and `oneLineStr` in `Decompress.lean`): binary `1ca0e023928ed2a520e888808de31ac60d8f7ed00ad0c4a5f152db1ab8b4996d` ran in 616 s (5 threads), 779 s (6 threads), and 1,378 s (2 threads), and binary `8daa81085f4b5dc1cb3bd2950e019f2e2b72b32457aba43c1ec8c9324642f377` ran in 744 s (5 threads). All five runs printed `s ALL VERIFIED n=48 k=24 cases=47580` with exit code 0, and their logs agree on every case in verdict, clauses, lemmas, hints, steps, and bytes.

## Limits of the program (robustness, not soundness)

* `qdcheck` is not hardened against adversarial certificates meant to waste resources: a numeral with several hundred thousand digits takes minutes to lex (the lexer is quadratic in digit count), and a lemma ID near 2^27 makes the renumbering table take 1 GB or more (about 2 GB peak observed). Neither can cause a false success line, and the SAT run certificates contain nothing like this.
* Content after the first empty clause is ignored, and deleting an unknown clause ID is skipped.
* `#print axioms` (`QueenDomCheck/Axioms.lean`) would not catch a declaration added with `set_option debug.skipKernelTC`. There is no `set_option` in `lean-sat` or `lean-check`. To verify this mechanically, replay the compiled modules through the kernel:
  * In `../lean-sat`: `lake env leanchecker QueenDomSat.Encode QueenDomSat.Cases QueenDomSat.Formula QueenDomSat.Lemmas`
  * Here: `lake env leanchecker QueenDomCheck.Stream QueenDomCheck.Formula QueenDomCheck.Combine QueenDomCheck.Verify QueenDomCheck.Lrat QueenDomCheck.Decompress QueenDomCheck.Axioms Main`

## Files

| File | Content | Role |
| --- | --- | --- |
| `QueenDomCheck/Stream.lean` | `Verified cnf` (checker state plus proof that refuting it refutes `cnf`), `Verified.step`, `Verified.runFrom` (runs the `LRAT.check` loop one step at a time using Std's step functions and lemmas), `checkChunks_sound` | proof-carrying |
| `QueenDomCheck/Formula.lean` | `BaseCNF` (converted base formula for one deficit vector, with proof that it equals `toCNF (mkBase ..).cls`), `prepare`, `caseFormula_eq` (`caseFormula n k cs = base ++ toCNF (extra clauses)`) | proof-carrying |
| `QueenDomCheck/Combine.lean` | `covers`, `forall_of_covers`, `combine` (combines per-case proofs into `∀ cs ∈ l, ..`) | proof-carrying |
| `QueenDomCheck/Verify.lean` | `checkStream`, `verifyCase`, `verifyList`, `verifyAll`; worker threads and logging | glue (`IO`) |
| `QueenDomCheck/Lrat.lean` | Converts LRAT text to gapless `IntAction`s (lexer and clause-ID renumbering) | untrusted |
| `QueenDomCheck/Decompress.lean` | Runs `zstd -dc`, either directly or via a decompression server process | untrusted |
| `QueenDomCheck/Axioms.lean` | `#print axioms` under `#guard_msgs` (build fails if axioms change) | check |
| `Main.lean` | The `qdcheck` executable | glue |
| `scripts/tests.py` | Test suite (positive tests, negative tests, prototype agreement) | tests |
| `scripts/run_check.py` | Runs `qdcheck` and writes the summary file with SHA-256 hashes of binary and sources | runner |

The Lean interface (all in `namespace QueenDomCheck`):

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

## How a success value comes about

1. `enumCases n k` builds the case list (47,580 cases for `(48, 24)`).
2. `jobs` worker threads (dedicated tasks inside one process) pull cases from a shared counter. For each case `cs`, a worker:
   * fetches the base formula for `cs`'s deficit vector. `BaseCNF.build` converts the clauses of `enc.Base` (about 130,000 to 240,000 clauses for `(48, 24)`, depending on the deficit vector) once per deficit vector per thread (11 deficit vectors for `(48, 24)`, handed out in groups) and keeps the proof `cnf = toCNF (mkBase n k dR dC dT dS).cls`.
   * calls `prepare` to append the frame-dependent clauses; `caseFormula_eq` (from `QueenDomSat.caseCNF_eq`) proves the result equals `caseFormula n k cs`.
   * runs `checkStream` to read the decompressed certificate chunk by chunk. The untrusted normalizer turns text into `IntAction`s, and `Verified.runFrom` feeds them to Std's `State.checkRup`, `checkRat`, `checkEmpty`, `add`, and `deleteMany`. The checker state maintains the invariant that refuting the current clause set refutes the original formula, using Std's soundness lemmas (`entails_clause_of_checkRup`, `unsat_of_unsat_of_checkRat`, `entails_deleteMany`, `entails_clause_empty_of_checkEmpty`, etc.). When the empty clause is derived, the worker holds a proof of `(caseFormula n k cs).Unsat` (`Prepared.unsat` transports it across the equality).
   The worker returns `(index, ⟨cs, proof⟩ : {cs // (caseFormula n k cs).Unsat})`.
3. The main thread places each result into its slot in an array matching the case list. `covers` verifies that slot `i` holds a verified case equal to the `i`-th case in the list, and `forall_of_covers` turns that check into `∀ cs ∈ enumCases n k, (caseFormula n k cs).Unsat`.
4. `Main.lean` prints `s ALL VERIFIED n=<n> k=<k> cases=<N>` and returns exit code 0 only in the `.ok` branch of matching on that proof value. Every other stdout line is a `c ...` comment written through `comment` and `oneLineStr`, which replace control characters with `?`. External strings (the certificate directory, `--cases` path, or OS and `zstd` error messages) therefore cannot inject a fake status line (test (f)).

Because Lean erases proofs at run time, "holding a proof" means the program type-checked in Lean's kernel when built, and the branch printing `s ALL VERIFIED` is reachable only when every runtime check (`checkRup .. = true`, `covers .. = true`, etc.) succeeded.

## What is trusted, what is not

Trusted:

* Lean's kernel (which checked every definition and proof in `lean-check`, `lean-sat`, and `Std` at build time) and the definitions in the statement: `QueenDomSat.enumCases`, `QueenDomSat.caseFormula` (unfolding to `mkBase`, `caseExtra`, `toCNF`, etc.), and `Std.Sat.CNF.Unsat`.
* Std's LRAT checker: `Std.Tactic.BVDecide.LRAT.Internal.State.{ofCNF, checkRup, checkRat, checkEmpty, add, deleteMany}` and their soundness lemmas. They are used unmodified, and the streaming driver in `Stream.lean` is proved from the same public lemmas as Std's own `LRAT.check_sound` (`checkChunks_sound`).
* The Lean compiler and runtime, the C compiler, the OS, and the hardware. Specifically, we trust that compiled code matches its definitions (encoder, case list, checker, and glue in `Verify.lean`, `Combine.lean`, and `Formula.lean`), including runtime primitives for arrays, natural numbers, hash maps, threads, reference counting, and the `implemented_by` and `extern` replacements inside core and Std (such as `Array.map` and clause iteration in `Std.Sat.CNF.Clause`). This matches the trust model of any `native_decide`-free Lean executable. None of `native_decide`, `sorry`, `axiom`, `unsafe`, `implemented_by`, `extern`, or `opaque` appear in this package's code (only in comments). Three loops in the untrusted lexer use `partial def`, and `while`/`repeat` loops appear in the lexer and `IO` code, including `checkStream`. The kernel type-checks the loop body of `checkStream` (returning `verified h` requires `h : cnf.Unsat`); trusting that the compiled loop executes that body is part of trusting the compiler.
* Standard axioms only: `propext`, `Classical.choice`, and `Quot.sound` (checked by `QueenDomCheck/Axioms.lean`; the build fails if others appear).

Not trusted (bugs here can cause a valid certificate to be rejected, never an invalid one to be accepted):

* The certificates, CaDiCaL, drat-trim, `enc.py`, `geom.py`, and the SAT run logs.
* Decompression (`zstd`, the decompression server processes, and framing between servers and checker).
* The LRAT lexer and clause-ID renumbering (`Lrat.lean`): drat-trim numbers lemmas by their position in the untrimmed proof while Std expects `m+1, m+2, ...`, and a 0-byte LRAT file for a formula already containing the empty clause gets completed with the single missing empty-clause step.
* Thread scheduling, base-formula caching, and slot assignment (the final `covers` check compares every slot against the case list).
* Logging, statistics, timing, and the summary script.

Not covered in this package: that `caseFormula` is satisfiable whenever a dominating set falls into a case (Layer 2, proved in `../Queens48`), and that the Lean encoder agrees with `enc.py` (not needed for the theorem; it just explains why Python-generated certificates match, and `lean-sat/scripts/compare_enc.py` verifies byte-for-byte agreement).

## Build, run, test

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

* Requires `zstd` on `PATH` (invoked as `zstd -dc -- FILE`).
* Output and exit codes: stdout has `c ...` comment lines followed by one final status line; check both the exit code and the status line (as `scripts/run_check.py` does). Passing `--version` anywhere prints the version and exits 0 without a status line. The internal `--decompress-server` flag streams decompressed bytes to stdout and never exits 0. For an empty case list (such as `(48, 23)` where no case is admissible), the program reads no certificates and prints `s ALL VERIFIED n=48 k=23 cases=0`, which is why the status line includes the case count. Exit codes:
  * `0`: `s ALL VERIFIED n=.. k=.. cases=..` (entire case list; never returned with `--limit` or `--cases`).
  * `1`: `s NOT VERIFIED ...` (all cases are tried; failed cases and reasons go to stderr, the log, and the first 200 to stdout).
  * `2`: usage error.
  * `3`: `s SUBSET VERIFIED ...` (every case selected by `--limit M` for the first `M` cases, or `--cases FILE` with 8 integers per line, passed; this does not certify the full case list even if the subset equals it).
* `--log FILE` writes one JSON line per case (`case`, `verdict` = `verified`/`failed`, `reason`, `clauses`, `lemmas`, `hints`, `steps`, `bytes` of LRAT text read, `zst_bytes`, `zstd_rc`, `cpu_ms` of the worker thread, `wall_ms`, `base_cpu_ms` if a base formula was built, and `worker`), followed by `{"summary": {...}}`, whose `all_verified` field is `true` only in the `s ALL VERIFIED` branch.
* Decompression: by default, each worker talks to a helper process (`qdcheck --decompress-server`, started before spawning threads) that invokes `zstd -dc` per certificate and frames the output. Forking from the multi-threaded checker itself costs more than checking a small certificate; `--direct-zstd` spawns `zstd` directly and was slower in every test.
* Memory: each thread holds the base formula for the current deficit vector (about 30 MB for n = 48), the live clauses of the active proof, and one 4 MiB read chunk.

## Tests (`scripts/tests.py`: 61 checks, 65 with `--proto`)

* (a) Complete instance `(n, k) = (8, 4)` (where γ(Q_8) = 5): `code/frame/run_cases48.py 8 4` generates all 195 certificates on the spot using CaDiCaL, drat-trim, and zstd. `qdcheck 8 4` returns `s ALL VERIFIED n=8 k=4 cases=195` with exit code 0 across 1 to 5 threads, chunk sizes of 1, 5, 7, and 4096 bytes, and both decompression modes. `--limit` and `--cases` always exit 3 and never print `s ALL VERIFIED`.
* (b) Satisfiable instance `(6, 3)`: 1 of the 98 cases is satisfiable and has no certificate. `qdcheck` exits 1 with no success line, even if that missing certificate is replaced by any of the other 97.
* (c) Negative tests on `(8, 4)`: missing, empty, damaged, or truncated certificates; proofs without the empty clause or with missing/incomplete hints; removed lemmas; removed or reversed hints; garbage bytes; and certificates from other cases (single, two swapped, or all rotated). Every test returns exit 1 and `s NOT VERIFIED`, while the valid cases still pass.
* (e) Formulas already containing the empty clause (non-admissible cases, where drat-trim writes a 0-byte LRAT file): verified using the added final step, whereas the same empty file is rejected for any formula without an empty clause. Unit-propagation refutations (deletion line plus empty clause) occur in 133 of 195 cases for `(8, 4)` and about half of `(48, 24)`.
* (f) Status-line forgery resistance: a certificate directory or `--cases` path containing a newline followed by `s ALL VERIFIED ...`, or a decompressor printing that line to stderr and failing, still exits 1 with exactly one `s ` line (`s NOT VERIFIED`), all other stdout lines prefixed by `c `, and no forged line on stderr. The internal decompression server exits 4 and rejects `n k CERTDIR`, and an empty case list prints `cases=0`.
* (d) Prototype comparison (only with `--proto`; the earlier standalone prototype is not in this repository, so these four checks cannot be run from this repo alone): compares against `lratcheck --stream` (which parses DIMACS files from `enc.py`) on 67 cases of `(48, 24)` spanning all 11 deficit vectors, confirming identical verdicts, lemma and hint counts, and byte counts, plus mutual rejection on 14 swapped certificates.
