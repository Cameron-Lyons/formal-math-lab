# lean-check: the certificates of the frame method, checked inside Lean

`qdcheck n k CERTDIR` checks, for every case `cs` of the case list `QueenDomSat.enumCases n k`, the
stored LRAT certificate `CERTDIR/<ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>.lrat.zst` against the formula
`QueenDomSat.caseFormula n k cs` **built by the Lean encoder** (`../lean-sat`), with the verified
LRAT checker of Lean's standard library (`Std.Tactic.BVDecide.LRAT`).  The program is written so that
it can only report success by constructing a value of the type

    PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)

which is the hypothesis of the theorem proved in `../Queens48`
(`(∀ cs ∈ QueenDomSat.enumCases 48 24, (QueenDomSat.caseFormula 48 24 cs).Unsat) → gamma 48 = 25`).
Neither the Python encoder `enc.py`, nor the case list of `geom.py`, nor the records of the SAT run
are read: the only input is the directory of certificates.

Package `QueenDomCheck`, Lean 4.35.0 (`lean-toolchain`), no Mathlib; the only dependency is the
Mathlib-free package `../lean-sat` (`QueenDomSat`: encoder, case list).

## Result for (n, k) = (48, 24)

Run of 2026-11-24 on the 47,580 certificates of `runs/d_48_24.jsonl.lrat` (25 GB compressed,
148.5 GB of LRAT text), 5 threads, on a machine that was busy with other work (first output line, with
the path of the directory, omitted; the command is written relative to the checkout):

    $ lean-check/.lake/build/bin/qdcheck 48 24 runs/d_48_24.jsonl.lrat --jobs 5 --log data/frame/lean_check_48_24.jsonl
    c case list: QueenDomSat.enumCases 48 24, 47580 cases
    c result: cases=47580 verified=47580 failed=0 zstd_warnings=0
    c proofs: lrat_bytes=148456520357 zst_bytes=24964196706 lemmas=122429776 hints=10891488639 base_formulas_built=55
    c time: wall_s=809.860 worker_cpu_s=2778.953 process_cpu_s=2807.000 decompress_cpu_s=431.280 peak_rss_kb=390372
    s ALL VERIFIED n=48 k=24 cases=47580

* exit code 0; 47,580 of 47,580 cases verified, none failed;
* wall time 810 s; CPU time 3,238 s (54 min) for `qdcheck` and all its children, of which 2,807 s
  the checker process and 431 s decompression; peak memory 390 MB (the whole process, 5 threads);
* the hardest case is (0,1,0,1,0,0,0,0): 2.25 GB of LRAT text, 2,390,553 lemmas, 75 s of CPU;
  22,753 cases are refuted by unit propagation alone (their proof is the empty clause with hints);
* files: `data/frame/lean_check_48_24.jsonl` (one line per case and the summary line),
  `data/frame/lean_check_48_24.summary.json` (totals, final line, SHA-256 of the binary
  `4388f9e49d7cfbf4168eb0ad7cb5193c8ffec6b808c223b8ca9307b2ba7656cb` and of the Lean sources of
  `lean-check` and `lean-sat`), `data/frame/lean_check_48_24.stdout.txt`.  A build of a fresh copy
  of the sources reproduces the binary bit for bit.
* cross-check (not needed for the claim): the cases of the log are exactly the cases of the records
  of the SAT run `runs/d_48_24.jsonl`, and for every case the number of bytes read equals the
  record's `lrat_bytes`.
* earlier runs of the same day, with two earlier versions of the program that differ from the present
  one only in how text is printed and in the exit code of the internal server mode (`Main.lean`,
  one line of `Verify.lean`, `oneLineStr` in `Decompress.lean`): binary
  `1ca0e023928ed2a520e888808de31ac60d8f7ed00ad0c4a5f152db1ab8b4996d`, 616 s with 5 threads, 779 s with
  6 and 1,378 s with 2; binary `8daa81085f4b5dc1cb3bd2950e019f2e2b72b32457aba43c1ec8c9324642f377`, 744 s
  with 5 threads.  All of them `s ALL VERIFIED n=48 k=24 cases=47580`, exit code 0; the logs of all five
  runs agree on every case in verdict, number of clauses, lemmas, hints, steps and bytes.

## Limits of the program (robustness, not soundness)

* `qdcheck` is not hardened against certificates written to waste resources: a numeral of several
  hundred thousand digits takes minutes to read (the lexer is quadratic in the number of digits), and
  a lemma id near 2^27 makes the renumbering table take 1 GB or more (about 2 GB peak was observed).  Neither leads to a success
  line; the certificates of the SAT run contain nothing of the kind.
* Content of a certificate after the first empty clause is not read; a deletion of an unknown clause
  id is skipped.
* `#print axioms` (`QueenDomCheck/Axioms.lean`) would not notice a declaration that was added with the
  kernel check switched off (`set_option debug.skipKernelTC`).  There is no `set_option` in the
  sources of `lean-sat` and `lean-check`; to rule it out mechanically, replay the compiled modules
  through the kernel: `lake env leanchecker QueenDomSat.Encode QueenDomSat.Cases QueenDomSat.Formula
  QueenDomSat.Lemmas` in `../lean-sat` and `lake env leanchecker QueenDomCheck.Stream
  QueenDomCheck.Formula QueenDomCheck.Combine QueenDomCheck.Verify QueenDomCheck.Lrat
  QueenDomCheck.Decompress QueenDomCheck.Axioms Main` here.

## Files

| file | content | role |
|---|---|---|
| `QueenDomCheck/Stream.lean` | `Verified cnf` (checker state + proof that refuting it refutes `cnf`), `Verified.step`, `Verified.runFrom`: the loop of `LRAT.check`, one step at a time, with Std's step functions and Std's lemmas; `checkChunks_sound` | proof-carrying |
| `QueenDomCheck/Formula.lean` | `BaseCNF` (the converted base formula of one deficit vector, with the proof that it is `toCNF (mkBase ..).cls`), `prepare`, `caseFormula_eq`: `caseFormula n k cs = base ++ toCNF (extra clauses)` | proof-carrying |
| `QueenDomCheck/Combine.lean` | `covers`, `forall_of_covers`, `combine`: from per-case results to `∀ cs ∈ l, ..` | proof-carrying |
| `QueenDomCheck/Verify.lean` | `checkStream`, `verifyCase`, `verifyList`, `verifyAll`; worker threads, log | glue (`IO`) |
| `QueenDomCheck/Lrat.lean` | LRAT text → gapless `IntAction`s (lexer, renumbering of clause ids) | untrusted |
| `QueenDomCheck/Decompress.lean` | `zstd -dc`, directly or through a decompression server process | untrusted |
| `QueenDomCheck/Axioms.lean` | `#print axioms` of the above under `#guard_msgs` (the build fails if they change) | check |
| `Main.lean` | the executable `qdcheck` | glue |
| `scripts/tests.py` | tests (positive, negative, agreement with the prototype) | |
| `scripts/run_check.py` | runs `qdcheck` and writes the summary file with the SHA-256 of binary and sources | |

The interface (all in `namespace QueenDomCheck`):

    def verifyCase (n k : Nat) (cs : CaseT) (b : BaseCNF n k) (hb : b.Matches cs) (proof : IO ByteArray) :
        IO (Verdict (caseFormula n k cs).Unsat × CaseInfo)
    def verifyCase' (n k : Nat) (cs : CaseT) (proof : IO ByteArray) :
        IO (Option (PLift (caseFormula n k cs).Unsat) × CaseInfo)
    def verifyList (n k : Nat) (l : List CaseT) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
        IO (Report × Option (PLift (∀ cs ∈ l, (caseFormula n k cs).Unsat)))
    def verifyAll (n k : Nat) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
        IO (Except String (PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)))

(`proof` returns the next chunk of LRAT text, the empty array at the end; `Verdict p` is
`verified (h : p) | failed (reason : String)`.)

## How a success value comes about

1. `enumCases n k` is computed (the list has 47,580 elements for (48, 24)).
2. `jobs` worker threads (dedicated tasks of one process) take cases from a shared counter.  For a
   case `cs` a worker
   * takes the base formula of the deficit vector of `cs`: `BaseCNF.build` converts the
     clauses of `enc.Base` (for (48, 24) about 130,000 to 240,000, depending on the deficit vector) once per deficit vector and thread (11 deficit vectors for (48, 24); the
     cases are handed out grouped by deficit vector) and keeps it together with the proof
     `cnf = toCNF (mkBase n k dR dC dT dS).cls`;
   * `prepare` appends the converted frame-dependent clauses; `caseFormula_eq` (from
     `QueenDomSat.caseCNF_eq`) proves that the result *is* `caseFormula n k cs`;
   * `checkStream` reads the decompressed certificate chunk by chunk; the untrusted normaliser turns
     the text into `IntAction`s; `Verified.runFrom` feeds them to Std's `State.checkRup` /
     `checkRat` / `checkEmpty` / `add` / `deleteMany`.  The state carries the invariant "a refutation
     of the current clause set refutes the formula", maintained with Std's lemmas
     (`entails_clause_of_checkRup`, `unsat_of_unsat_of_checkRat`, `entails_deleteMany`,
     `entails_clause_empty_of_checkEmpty`, ...), so when the empty clause is derived the worker holds a
     proof of `(caseFormula n k cs).Unsat` (`Prepared.unsat` transports it along the equality).
   The worker returns pairs (position in the list, `⟨cs, proof⟩ : {cs // (caseFormula n k cs).Unsat}`).
3. The main thread puts the results into one slot per position of the case list; `covers` checks
   that slot `i` holds a verified case *equal* to the `i`-th case of the list, and
   `forall_of_covers` turns this into `∀ cs ∈ enumCases n k, (caseFormula n k cs).Unsat`.
4. `Main.lean` prints `s ALL VERIFIED n=<n> k=<k> cases=<N>` in the `.ok` branch of a `match` on that
   value and nowhere else, and only there returns the exit code 0.  Every other line of the standard
   output of a run is a comment line `c ...` written through `comment` / `oneLineStr`, which replace
   control characters by `?`: text that comes from outside (the name of the certificate directory or
   of the `--cases` file, error messages of the operating system or of `zstd`) cannot start a line,
   so it cannot produce a line that looks like a status line (test (f)).

Proofs are erased at run time, so "holds a proof" means: the program is well typed (checked by the
Lean kernel when the package is built), and the branch that prints the success line can only be
reached through the branches in which the run-time tests (`checkRup ..= true`, `covers ..= true`, ...)
came out true.

## What is trusted, what is not

Trusted:

* **Lean's kernel** (it checked every definition and proof of `lean-check`, `lean-sat` and `Std`
  when they were built) and the **definitions** the statement is about: `QueenDomSat.enumCases`,
  `QueenDomSat.caseFormula` (and what they unfold to: `mkBase`, `caseExtra`, `toCNF`, ...),
  `Std.Sat.CNF.Unsat`.
* **Std's LRAT checker**: the functions `Std.Tactic.BVDecide.LRAT.Internal.State.{ofCNF, checkRup,
  checkRat, checkEmpty, add, deleteMany}` and their soundness lemmas.  They are used unchanged; the
  streaming driver around them (`Stream.lean`) is proved from the same public lemmas as
  Std's own `LRAT.check_sound` (`checkChunks_sound`).
* **The Lean compiler and runtime**: that the compiled code computes what the definitions say
  (encoder, case list, checker, the glue in `Verify.lean` / `Combine.lean` / `Formula.lean`),
  including the runtime's built-in implementations of arrays, natural numbers, hash maps, the
  `implemented_by` / `extern` replacements inside core and Std (e.g. `Array.map`, the iteration over
  a clause in `Std.Sat.CNF.Clause`), threads and reference counting; the C compiler, OS and hardware.
  This is the same trust as for any `native_decide`-free executable written in Lean; none of the
  keywords `native_decide`, `sorry`, `axiom`, `unsafe`, `implemented_by`, `extern`, `opaque` occurs
  in the code of this package (comments mention some).  `partial def` occurs in three loops of the
  untrusted lexer, and `while` / `repeat` loops occur in the lexer and in `IO` code.  The loop of
  `checkStream` is one of them: it carries the checker state with its invariant and returns, on
  success, a verdict that contains the proof.  The kernel has type-checked its body (a verdict
  `verified h` needs a term `h : cnf.Unsat`); that the compiled loop runs that body is part of the
  trust in the compiler.
* Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`QueenDomCheck/Axioms.lean`; the build
  fails otherwise).

Not trusted (a mistake there can turn a valid certificate into a rejected one, never the converse):

* the certificates themselves, cadical, drat-trim, `enc.py`, `geom.py`, the records of the SAT run;
* decompression (`zstd`, the decompression servers, the framing between them and the checker);
* the LRAT lexer and the renumbering of the clause ids (`Lrat.lean`): drat-trim numbers the lemmas
  by their position in the untrimmed proof, Std's checker wants the ids `m+1, m+2, ...`; an empty
  LRAT file for a formula that contains the empty clause is completed by the one missing step;
* scheduling: which thread checks which case in which order, the cache of base formulas, the
  placement of the results into the slots (the final `covers` test compares every slot with the
  case list);
* logging, statistics, time measurement, the summary script.

Not covered here: that `caseFormula` is satisfiable whenever a dominating set falls into the case
(Layer 2, proved in `../Queens48`), and that the Lean encoder agrees with `enc.py`
(irrelevant for the theorem; it is the reason why the certificates of the Python run fit, and
`lean-sat/scripts/compare_enc.py` compares the two byte by byte).

## Build, run, test

    lake build                                   # in this directory; builds ../lean-sat if necessary
    .lake/build/bin/qdcheck 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 --log LOG.jsonl
    python3 -I scripts/run_check.py 48 24 ../runs/d_48_24.jsonl.lrat --jobs 5 \
        --log ../data/frame/lean_check_48_24.jsonl --summary ../data/frame/lean_check_48_24.summary.json \
        --out ../data/frame/lean_check_48_24.stdout.txt
    python3 -I scripts/tests.py WORKDIR [--proto PATH/lratcheck]

    qdcheck n k CERTDIR [--jobs N] [--log FILE] [--limit M | --cases FILE]
                        [--chunk-mib N] [--zstd CMD] [--direct-zstd] [--progress N]

* Needs `zstd` in the `PATH` (called as `zstd -dc -- FILE`).
* Standard output: `c ...` lines and one status line, the last line.  Rely on the exit code together
  with that line (as `scripts/run_check.py` does).  `--version`, anywhere among the arguments, prints
  the version and exits with 0 without a status line; `--decompress-server` (internal) copies
  decompressed bytes to the standard output and never exits with 0.  If the case list is empty (for instance
  (48, 23): no case is admissible) the program reads nothing and prints
  `s ALL VERIFIED n=48 k=23 cases=0`, the true but empty statement about no formula; the number of
  cases is part of the status line for that reason.  Exit code
  **0**: `s ALL VERIFIED n=.. k=.. cases=..` (the whole case list; never with `--limit` / `--cases`);
  **1**: `s NOT VERIFIED ...` (all cases are tried; each failed case is reported with its reason on
  stderr, in the log, and the first 200 on stdout);
  **2**: usage error;
  **3**: `s SUBSET VERIFIED ...`: every case of the subset given by `--limit M` (the first `M` cases
  of the list) or `--cases FILE` (8 integers per line) was verified; this is *not* the statement
  about the case list, also when the subset happens to be the whole list.
* `--log FILE`: one JSON line per case
  (`case`, `verdict` = `verified` / `failed`, `reason`, `clauses`, `lemmas`, `hints`, `steps`, `bytes`
  = LRAT text read, `zst_bytes`, `zstd_rc`, `cpu_ms` = CPU time of the worker thread for this case,
  `wall_ms`, `base_cpu_ms` if a base formula was built, `worker`), then one line
  `{"summary": {...}}`; its field `all_verified` is `true` only in the branch that also prints
  `s ALL VERIFIED`.
* Decompression: by default each worker thread talks to a helper process
  (`qdcheck --decompress-server`, started before the threads) that spawns `zstd -dc` per certificate
  and relays its output in frames, because a `fork` of the multi-threaded checker itself costs more
  than checking a small certificate (`--direct-zstd` spawns `zstd` from the checker process; it was
  slower in every comparison made).
* Memory: the base formula of the current deficit vector (about 30 MB for n = 48), the live clauses
  of the proof being checked and one chunk (4 MiB) per thread.

## Tests (`scripts/tests.py`: 61 checks, 65 with `--proto`)

* (a) (n, k) = (8, 4), a complete instance (γ(Q_8) = 5): the 195 certificates are produced on the
  spot by `code/frame/run_cases48.py 8 4` (cadical, drat-trim, zstd, as in the real run);
  `qdcheck 8 4` gives `s ALL VERIFIED n=8 k=4 cases=195`, exit 0, with 1–5 threads, chunks of 1, 5, 7,
  4096 bytes, both decompression modes; `--limit` / `--cases` give exit 3 and never the full claim.
* (b) (6, 3) is satisfiable: 1 of the 98 cases has a model and no certificate; exit 1, no success
  line; also when the missing certificate is replaced by any of the 97 others.
* (c) negative tests on (8, 4): certificate missing, empty, damaged, truncated, without the empty
  clause, empty clause without hints / without its last hint, a used lemma removed, hints removed
  or reversed, garbage, certificates of other cases (one, two swapped, all rotated): exit 1 and
  `s NOT VERIFIED` every time, the other cases are still verified.
* (e) formulas containing the empty clause (non-admissible cases; drat-trim writes an LRAT file of
  0 bytes): verified through the supplied final step; the same empty file fails for a formula
  without an empty clause.  Refutations by unit propagation alone (deletion line + empty clause)
  occur in (8, 4) (133 of 195 cases) and in about half of the (48, 24) cases.
* (f) the status line cannot be forged from outside: a certificate directory or a `--cases` file
  whose name contains a newline followed by `s ALL VERIFIED ...`, and a decompressor that prints
  such a line on its error output and fails: exit 1, exactly one line starting with `s `
  (`s NOT VERIFIED`), every other line a comment; no such line on stderr either; the internal
  decompression server ends with exit code 4 and refuses the arguments `n k CERTDIR`; an empty case
  list gives `cases=0`.
* (d) (only with `--proto`; the prototype is an earlier stand-alone checker that is not part of this
  repository, so these four checks cannot be repeated from the repository alone)
  agreement with the prototype `lratcheck --stream` (which parses the DIMACS file written by
  `enc.py`) on a sample of 67 cases of (48, 24) covering all 11 deficit vectors: same verdict, same
  numbers of lemmas and hints, the byte counts of the records; and on 14 swapped certificates both
  reject.
