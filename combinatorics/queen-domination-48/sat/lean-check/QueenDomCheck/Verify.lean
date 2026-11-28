/-
The certificate checker: `verifyCase` (one case), `verifyList` (a list of cases, in parallel),
`verifyAll` (the case list `QueenDomSat.enumCases n k`).

What the types say.  `verifyAll n k certDir jobs` returns, on success, a value of

    PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)

i.e. the hypothesis of the final theorem.  Such a value can only be built from a proof, and the
proof is assembled from

  * `Verified.runFrom` (`Stream.lean`): Std's verified LRAT step functions, giving `cnf.Unsat` for
    the formula `cnf` the checker was started on;
  * `Prepared.unsat` (`Formula.lean`): that formula is `caseFormula n k cs`;
  * `forall_of_covers` (`Combine.lean`): every case of the list has been settled.

Everything else in this file is plumbing whose mistakes can only lose a proof, never make one:
reading and decompressing the certificates (`zstd -dc`), lexing and renumbering (`Lrat.lean`), the
distribution of the cases over the worker threads, logging and statistics.
-/
import QueenDomCheck.Lrat
import QueenDomCheck.Stream
import QueenDomCheck.Formula
import QueenDomCheck.Combine
import QueenDomCheck.Decompress
import Std.Sync.Mutex

namespace QueenDomCheck
open QueenDomSat
open Std.Sat
open Std.Tactic.BVDecide.LRAT (IntAction)

/-- The result of a check of the proposition `p`: `verified` cannot be built without a proof. -/
inductive Verdict (p : Prop) where
  | verified (h : p)
  | failed (reason : String)

def Verdict.isVerified {p : Prop} : Verdict p → Bool
  | .verified _ => true
  | .failed _ => false

def Verdict.toOption {p : Prop} : Verdict p → Option (PLift p)
  | .verified h => some ⟨h⟩
  | .failed _ => none

/-- The statement that is established for one case. -/
abbrev CaseUnsat (n k : Nat) (cs : CaseT) : Prop := (caseFormula n k cs).Unsat

/-! ### Clocks (Linux: read from /proc; 0 if not available) -/

/-- CPU time (user + system) of the calling thread in nanoseconds. -/
def threadCpuNs : IO Nat := do
  try
    -- "time on cpu (ns)  time waiting on a run queue (ns)  number of time slices"
    let s ← IO.FS.readFile "/proc/thread-self/schedstat"
    match (s.splitOn " ").head?.bind String.toNat? with
    | some ns => return ns
    | none => return 0
  catch _ => return 0

/-- `(cpu, children)`: user + system CPU time in ms of this process (all threads) and of its
waited-for children (the `zstd` processes). -/
def processCpuMs : IO (Nat × Nat) := do
  try
    let s ← IO.FS.readFile "/proc/self/stat"
    -- pid (comm) state ppid ...; utime, stime, cutime, cstime are the fields 14-17, in ticks of 10 ms
    let rest := (s.splitOn ") ").getLast!
    let f := (rest.splitOn " ").toArray
    return ((f[11]!.toNat! + f[12]!.toNat!) * 10, (f[13]!.toNat! + f[14]!.toNat!) * 10)
  catch _ => return (0, 0)

/-- Peak resident set size of this process in kB. -/
def peakRssKb : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    for line in s.splitOn "\n" do
      if line.startsWith "VmHWM:" then
        return (String.ofList (line.toList.filter Char.isDigit)).toNat!
    return 0
  catch _ => return 0

/-! ### One formula, one proof stream -/

@[noinline] def feedIO (p : Parser) (buf : ByteArray) : IO Parser :=
  pure (p.feed buf)

@[noinline] def runBatchIO {cnf : CNF Nat} (v : Verified cnf) (steps : Array IntAction) :
    IO (Verified.BatchResult cnf) :=
  pure (v.runFrom steps 0)

/-- What was read while checking one proof.  Informational. -/
structure StreamInfo where
  /-- bytes of LRAT text read -/
  bytes : Nat := 0
  /-- counters of the normaliser -/
  lrat : Stats := {}
  /-- normalised steps accepted by the checker -/
  steps : Nat := 0
  deriving Inhabited

/--
Check an LRAT proof of `cnf`, given as a stream of text (`read` returns the next chunk, the empty
array at the end), chunk by chunk: the steps are normalised (untrusted), checked by Std's step
functions (`Verified.runFrom`) and discarded.  Memory: the live clauses and one chunk.

`emptyId` is the 1-based position of an empty clause of `cnf` (0: none); it is only handed to the
normaliser.  The stream is always read to its end.
-/
def checkStream (cnf : CNF Nat) (emptyId : Nat) (read : IO ByteArray) :
    IO (Verdict cnf.Unsat × StreamInfo) := do
  let mut p := Parser.new cnf.clauses.size true emptyId
  let mut v := Verified.init cnf
  let mut verdict : Option (Verdict cnf.Unsat) := none
  let mut stepsDone := 0
  let mut bytes := 0
  let mut eof := false
  repeat
    let buf ← read
    if buf.isEmpty then
      p := p.finish
      eof := true
    else
      bytes := bytes + buf.size
      p ← feedIO p buf
    let (steps, p') := p.drain
    p := p'
    let n := steps.size
    -- the steps read before a syntax error are still checked, the error is reported afterwards
    match ← runBatchIO v steps with
    | .more v' => v := v'
    | .unsat h =>
      stepsDone := stepsDone + n
      verdict := some (.verified h); break
    | .rejected idx =>
      stepsDone := stepsDone + idx
      verdict := some (.failed s!"step {stepsDone + 1} of the normalised proof was rejected by the LRAT checker")
      break
    stepsDone := stepsDone + n
    if let some e := p.norm.err then
      verdict := some (.failed e); break
    if eof then break
  -- the rest of the stream: read (so that the decompressor terminates normally and the byte count
  -- is complete) and, as long as it parses, counted; nothing of it is checked
  unless eof do
    repeat
      let buf ← read
      if buf.isEmpty then break
      bytes := bytes + buf.size
      unless p.norm.err.isSome do
        p ← feedIO p buf
        p := (p.drain).2
    p := p.finish
  let result := verdict.getD (.failed "the proof ends without an empty clause")
  return (result, { bytes, lrat := p.norm.stats, steps := stepsDone })

/-! ### One case -/

/-- Numbers about one case.  Informational. -/
structure CaseInfo where
  /-- clauses of the formula -/
  clauses : Nat := 0
  stream : StreamInfo := {}
  /-- size of the compressed certificate -/
  zstBytes : Nat := 0
  /-- exit code of the decompressor (0 also when it was not run) -/
  zstdRc : Nat := 0
  /-- CPU time of the checking thread for this case, without the construction of a base formula -/
  cpuNs : Nat := 0
  wallNs : Nat := 0
  /-- CPU time for the construction of the base formula, if this case needed a new one -/
  baseNs : Nat := 0
  deriving Inhabited

/--
**One case.**  Check the LRAT proof `proof` (a stream of text) against the formula
`caseFormula n k cs`, which is built from the shared base formula `b` of the deficit vector of `cs`.
-/
def verifyCase (n k : Nat) (cs : CaseT) (b : BaseCNF n k) (hb : b.Matches cs) (proof : IO ByteArray) :
    IO (Verdict (CaseUnsat n k cs) × CaseInfo) := do
  let p := prepare b cs hb
  let clauses := p.cnf.clauses.size
  let (v, info) ← checkStream p.cnf p.emptyId proof
  match v with
  | .verified h => return (.verified (p.unsat h), { clauses, stream := info })
  | .failed r => return (.failed r, { clauses, stream := info })

/-- `verifyCase` in the shape `Option (PLift _)`, building the base formula itself. -/
def verifyCase' (n k : Nat) (cs : CaseT) (proof : IO ByteArray) :
    IO (Option (PLift (caseFormula n k cs).Unsat) × CaseInfo) := do
  let (v, info) ← verifyCase n k cs (.build n k cs.dR cs.dC cs.dT cs.dS) (BaseCNF.matches_build n k cs) proof
  return (v.toOption, info)

/-- The base formula for `cs`: the cached one if it has the right deficit vector, else a new one. -/
def baseFor {n k : Nat} (cache : Option (BaseCNF n k)) (cs : CaseT) :
    {b : BaseCNF n k // b.Matches cs} × Bool :=
  match cache with
  | some b =>
    if h : b.Matches cs then (⟨b, h⟩, false)
    else (⟨.build n k cs.dR cs.dC cs.dT cs.dS, BaseCNF.matches_build n k cs⟩, true)
  | none => (⟨.build n k cs.dR cs.dC cs.dT cs.dS, BaseCNF.matches_build n k cs⟩, true)

/-- `baseFor`, executed where it is called (so that the construction of a base formula is timed). -/
@[noinline] def baseForIO {n k : Nat} (cache : Option (BaseCNF n k)) (cs : CaseT) :
    IO ({b : BaseCNF n k // b.Matches cs} × Bool) :=
  pure (baseFor cache cs)

/-! ### Many cases -/

/-- Options of a run. -/
structure Options where
  /-- per-case JSON lines are appended to this file -/
  log : Option System.FilePath := none
  /-- bytes per read of the decompressed stream -/
  chunk : USize := 4 * 1024 * 1024
  /-- the decompressor; called as `zstd -dc -- FILE` -/
  zstd : String := "zstd"
  /-- command and arguments of a decompression server (`Decompress.lean`), one of which is started
  per worker thread; `none`: every certificate is decompressed by a `zstd` process spawned by the
  checker process itself -/
  server : Option (String × Array String) := none
  /-- print a progress line to stderr every so many cases (0: never) -/
  progressEvery : Nat := 1000
  /-- at most this many failures are kept with their reasons in the report (all are in the log) -/
  maxFailures : Nat := 200

/-- Totals of a run.  Informational. -/
structure Report where
  n : Nat := 0
  k : Nat := 0
  jobs : Nat := 0
  cases : Nat := 0
  verified : Nat := 0
  failed : Nat := 0
  /-- the first failures, with their reasons -/
  failures : Array (CaseT × String) := #[]
  /-- verified cases whose decompressor did not exit with 0 -/
  zstdWarnings : Nat := 0
  lratBytes : Nat := 0
  zstBytes : Nat := 0
  lemmas : Nat := 0
  hints : Nat := 0
  /-- base formulas built (once per deficit vector and worker thread) -/
  baseBuilds : Nat := 0
  /-- sum of the CPU times of the worker threads, ms (per-case times and base formulas) -/
  workerCpuMs : Nat := 0
  /-- CPU time, ms, of the whole process, and of its child processes that have been waited for
  (the decompression servers with their `zstd` processes, or the `zstd` processes) -/
  processCpuMs : Nat := 0
  childCpuMs : Nat := 0
  wallMs : Nat := 0
  peakRssKb : Nat := 0
  deriving Inhabited

/-- Shared state of the worker threads. -/
structure Shared where
  certDir : System.FilePath
  opts : Options
  /-- position in the work order of the next case to hand out -/
  next : IO.Ref Nat
  report : IO.Ref Report
  log : Option IO.FS.Handle
  lock : Std.BaseMutex
  start : Nat

def withLock {α : Type} (lock : Std.BaseMutex) (act : IO α) : IO α := do
  lock.lock
  try act finally lock.unlock

def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n"
    else if c.toNat < 32 || c.toNat > 126 then acc ++ "?"
    else acc.push c

def caseJson (cs : CaseT) : String :=
  "[" ++ ",".intercalate (cs.toList.map toString) ++ "]"

/-- The log line of one case. -/
def logLine (cs : CaseT) (verdict : String) (reason : Option String) (info : CaseInfo) (worker : Nat) :
    String :=
  let st := info.stream.lrat
  "{\"case\":" ++ caseJson cs ++ ",\"verdict\":\"" ++ verdict ++ "\"" ++
    (match reason with
     | some r => ",\"reason\":\"" ++ jsonEscape r ++ "\""
     | none => "") ++
    s!",\"clauses\":{info.clauses},\"lemmas\":{st.lemmas},\"hints\":{st.hints},\"steps\":{info.stream.steps}" ++
    s!",\"bytes\":{info.stream.bytes},\"zst_bytes\":{info.zstBytes},\"zstd_rc\":{info.zstdRc}" ++
    s!",\"cpu_ms\":{info.cpuNs / 1000000},\"wall_ms\":{info.wallNs / 1000000}" ++
    (if info.baseNs != 0 then s!",\"base_cpu_ms\":{info.baseNs / 1000000}" else "") ++
    s!",\"worker\":{worker}}\n"

/--
One case with its certificate file `certDir/<tag>.lrat.zst`, decompressed by `zstd -dc` (spawned
here, or by the decompression server `dec` of this thread) and streamed into `verifyCase`.  Never
throws: every error is a failed verdict.  The last component says that `dec` has to be replaced.
-/
def runCase (n k : Nat) (sh : Shared) (dec : Option Decompressor) (cs : CaseT) (b : BaseCNF n k)
    (hb : b.Matches cs) : IO (Verdict (CaseUnsat n k cs) × CaseInfo × Bool) := do
  let t0 ← IO.monoNanosNow
  let c0 ← threadCpuNs
  let finish (r : Verdict (CaseUnsat n k cs) × CaseInfo) (zstBytes zstdRc : Nat) (broken : Bool) :
      IO (Verdict (CaseUnsat n k cs) × CaseInfo × Bool) := do
    let c1 ← threadCpuNs
    let t1 ← IO.monoNanosNow
    return (r.1, { r.2 with zstBytes, zstdRc, cpuNs := c1 - c0, wallNs := t1 - t0 }, broken)
  try
    let path := sh.certDir / (cs.tag ++ ".lrat.zst")
    unless ← path.pathExists do
      return ← finish (.failed s!"certificate file {path} does not exist", {}) 0 0 false
    let zstBytes := (← path.metadata).byteSize.toNat
    -- (zstd ignores symbolic links, so the link is resolved here)
    let real ← IO.FS.realPath path
    let (req, stream) ← match dec with
      | some d => do
        let (req, stream) ← d.request real
        pure (some req, stream)
      | none => do
        pure (none, ← ProofStream.direct sh.opts.zstd real sh.opts.chunk)
    let (v, info) ← verifyCase n k cs b hb stream.read
    -- `verifyCase` has read the stream to its end
    let (rc, err) ← stream.finish
    let broken ← match req with
      | some r => do pure (← r.get).broken
      | none => pure false
    match v with
    | .verified h => finish (.verified h, info) zstBytes rc broken
    | .failed r =>
      let r := if rc == 0 then r else r ++ s!" (zstd exit code {rc}: {err})"
      finish (.failed r, info) zstBytes rc broken
  catch e =>
    finish (.failed s!"error: {e}", {}) 0 0 dec.isSome

/--
A worker thread: takes the next position of the work order until none is left, and returns the
cases it has verified, each with its position in `cases` and the proof.  The base formula of the
current deficit vector is kept (and belongs to this thread alone, so that the reference counts of
its clauses are not shared between threads).
-/
def worker (n k : Nat) (sh : Shared) (cases : Array CaseT) (order : Array Nat) (wid : Nat)
    (dec0 : Option Decompressor) : IO (Array (Nat × {cs : CaseT // CaseUnsat n k cs})) := do
  let mut cache : Option (BaseCNF n k) := none
  let mut out : Array (Nat × {cs : CaseT // CaseUnsat n k cs}) := #[]
  -- the decompression server of this thread
  let mut dec : Option Decompressor := dec0
  let mut restarts := 0
  repeat
    let j ← sh.next.modifyGet fun j => (j, j + 1)
    if hj : j < order.size then
      let i := order[j]
      if hi : i < cases.size then
        let cs := cases[i]
        let c0 ← threadCpuNs
        let (⟨b, hb⟩, built) ← baseForIO cache cs
        cache := some b
        let baseNs ← if built then (do pure (max 1 ((← threadCpuNs) - c0))) else pure 0
        if dec.isNone then
          if let some (cmd, args) := sh.opts.server then
            -- the server has been lost: a new one (after 3 losses this thread spawns `zstd` itself)
            if restarts < 3 then
              try dec := some (← Decompressor.start cmd args) catch _ => pure ()
              restarts := restarts + 1
        let (v, info, broken) ← runCase n k sh dec cs b hb
        if broken then
          if let some d := dec then d.stop
          dec := none
        let info := { info with baseNs }
        let st := info.stream.lrat
        let (ok, reason) := match v with
          | .verified _ => (true, none)
          | .failed r => (false, some r)
        if let .verified h := v then
          out := out.push (i, ⟨cs, h⟩)
        let line := logLine cs (if ok then "verified" else "failed") reason info wid
        let rep ← sh.report.modifyGet fun r =>
          let r := { r with
            verified := r.verified + (if ok then 1 else 0)
            failed := r.failed + (if ok then 0 else 1)
            failures :=
              match reason with
              | some why => if r.failures.size < sh.opts.maxFailures then r.failures.push (cs, why) else r.failures
              | none => r.failures
            zstdWarnings := r.zstdWarnings + (if ok && info.zstdRc != 0 then 1 else 0)
            lratBytes := r.lratBytes + info.stream.bytes
            zstBytes := r.zstBytes + info.zstBytes
            lemmas := r.lemmas + st.lemmas
            hints := r.hints + st.hints
            baseBuilds := r.baseBuilds + (if built then 1 else 0)
            workerCpuMs := r.workerCpuMs + (info.cpuNs + info.baseNs) / 1000000 }
          (r, r)
        withLock sh.lock do
          if let some h := sh.log then
            h.putStr line
            h.flush
          if let some why := reason then
            IO.eprintln (oneLineStr s!"c FAILED case {cs.tag}: {why}")
          let done := rep.verified + rep.failed
          if sh.opts.progressEvery != 0 && done % sh.opts.progressEvery == 0 then
            let now ← IO.monoNanosNow
            IO.eprintln s!"c progress: {done}/{rep.cases} cases, verified={rep.verified} failed={rep.failed} lrat_gb={rep.lratBytes / 1000000000} elapsed_s={(now - sh.start) / 1000000000}"
    else break
  if let some d := dec then d.stop
  return out

/-- The work order: the positions of `cases`, grouped by deficit vector (in the order of first
appearance) and otherwise in list order.  Untrusted: only affects how often a base formula has to
be built. -/
def workOrder (cases : Array CaseT) : Array Nat := Id.run do
  let dv (cs : CaseT) : Nat × Nat × Nat × Nat := (cs.dR, cs.dC, cs.dT, cs.dS)
  let mut dvs : Array (Nat × Nat × Nat × Nat) := #[]
  for cs in cases do
    unless dvs.contains (dv cs) do dvs := dvs.push (dv cs)
  let mut order : Array Nat := Array.emptyWithCapacity cases.size
  for d in dvs do
    for h : i in [0:cases.size] do
      if dv cases[i] == d then order := order.push i
  return order

/--
**A list of cases.**  Checks the certificate of every case of `l` with `jobs` worker threads (all
cases are tried, also after a failure) and returns the totals together with, if every case was
verified, the proof of `∀ cs ∈ l, (caseFormula n k cs).Unsat`.
-/
def verifyList (n k : Nat) (l : List CaseT) (certDir : System.FilePath) (jobs : Nat)
    (opts : Options := {}) : IO (Report × Option (PLift (∀ cs ∈ l, CaseUnsat n k cs))) := do
  let jobs := max 1 jobs
  let cases := l.toArray
  let order := workOrder cases
  let start ← IO.monoNanosNow
  let (p0, ch0) ← processCpuMs
  let log ← match opts.log with
    | some f => some <$> IO.FS.Handle.mk f .write
    | none => pure none
  let sh : Shared := {
    certDir, opts, log, start
    next := ← IO.mkRef 0
    report := ← IO.mkRef { n, k, jobs, cases := cases.size }
    lock := ← Std.BaseMutex.new }
  -- the decompression servers, started now, while this process is small and has one thread
  let servers ← (List.range jobs).mapM fun _ => do
    match opts.server with
    | some (cmd, args) => try some <$> Decompressor.start cmd args catch _ => pure none
    | none => pure none
  -- the workers, each on a thread of its own
  let tasks ← (servers.zipIdx).mapM fun (dec, w) =>
    IO.asTask (worker n k sh cases order w dec) .dedicated
  let mut slots : Array (Option {cs : CaseT // CaseUnsat n k cs}) := Array.replicate cases.size none
  let mut crashed : Array String := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok results =>
      for (i, r) in results do
        slots := slots.setIfInBounds i (some r)
    | .error e => crashed := crashed.push (toString e)
  -- the statement about the whole list: every position of `l` must hold its own verified case
  let result := combine (CaseUnsat n k) l slots.toList
  let stop ← IO.monoNanosNow
  let (p1, ch1) ← processCpuMs
  let rss ← peakRssKb
  let rep ← sh.report.get
  let rep := { rep with
    processCpuMs := p1 - p0, childCpuMs := ch1 - ch0, wallMs := (stop - start) / 1000000, peakRssKb := rss
    failures := rep.failures ++ crashed.map fun e => (⟨0, 0, 0, 0, 0, 0, 0, 0⟩, s!"worker thread crashed: {e}") }
  return (rep, result)

/-- `verifyAll` together with the totals of the run. -/
def verifyAllReport (n k : Nat) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
    IO (Report × Except String
      (PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat))) := do
  let (rep, r) ← verifyList n k (enumCases n k) certDir jobs opts
  match r with
  | some h => return (rep, .ok h)
  | none =>
    return (rep, .error s!"{rep.failed} of {rep.cases} cases not verified ({rep.verified} verified)")

/--
**The whole case list.**  On success the result is the hypothesis of the final theorem: every case
of `QueenDomSat.enumCases n k` (computed here, not read from anywhere) has an unsatisfiable formula
`QueenDomSat.caseFormula n k cs`.  The certificate of the case `cs` is the file
`certDir/<cs.tag>.lrat.zst`.
-/
def verifyAll (n k : Nat) (certDir : System.FilePath) (jobs : Nat) (opts : Options := {}) :
    IO (Except String
      (PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat))) :=
  return (← verifyAllReport n k certDir jobs opts).2

end QueenDomCheck
