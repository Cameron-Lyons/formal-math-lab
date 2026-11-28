/-
qdcheck: check the LRAT certificates of the frame method for (n, k) with the verified LRAT checker of
Lean's standard library, against the formulas of the Lean encoder `QueenDomSat`.

  qdcheck n k CERTDIR [--jobs N] [--log FILE] [--limit M | --cases FILE]
                      [--chunk-mib N | --chunk-bytes N] [--zstd CMD] [--direct-zstd] [--progress N]
  qdcheck --version
  qdcheck --decompress-server [--zstd CMD] [--chunk-bytes N]      (internal, see Decompress.lean)

Without `--limit` / `--cases` the program runs `QueenDomCheck.verifyAll n k CERTDIR jobs` and prints

    s ALL VERIFIED n=<n> k=<k> cases=<number of cases>

only in the branch of a `match` that has received a value of type
`PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)`.

Exit code: 0  the statement above was established (all cases, never with `--limit` / `--cases`);
           1  some case was not verified;
           2  usage error;
           3  `--limit` / `--cases`: all cases of the subset were verified (not the full statement);
           4  end of `--decompress-server` (internal; refuses the arguments `n k CERTDIR`).
`--version` prints the version, no status line, and has exit code 0.
-/
import QueenDomCheck

open QueenDomCheck QueenDomSat

structure Args where
  pos : Array String := #[]
  jobs : Nat := 1
  log : Option String := none
  limit : Option Nat := none
  casesFile : Option String := none
  chunkBytes : Nat := 4 * 1024 * 1024
  zstd : String := "zstd"
  progress : Nat := 1000
  version : Bool := false
  serve : Bool := false
  direct : Bool := false

def usage : String :=
  "usage: qdcheck n k CERTDIR [--jobs N] [--log FILE] [--limit M | --cases FILE]\n" ++
  "                           [--chunk-mib N] [--zstd CMD] [--direct-zstd] [--progress N]\n" ++
  "  CERTDIR        directory with the certificates <ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>.lrat.zst\n" ++
  "  --jobs N       number of worker threads (default 1)\n" ++
  "  --log FILE     write one JSON line per case, and a summary line, to FILE\n" ++
  "  --limit M      check only the first M cases of the case list   (subset: exit code 3 at best)\n" ++
  "  --cases FILE   check only the cases listed in FILE, 8 integers per line (subset: exit code 3 at best)\n" ++
  "  --chunk-mib N  bytes per read of a decompressed certificate, in MiB (default 4)\n" ++
  "  --chunk-bytes N  the same in bytes (for tests of the chunk boundary handling)\n" ++
  "  --zstd CMD     the decompressor, called as CMD -dc -- FILE (default zstd)\n" ++
  "  --direct-zstd  spawn the decompressor from the checker process itself (slower with many threads;\n" ++
  "                 default: through one helper process `qdcheck --decompress-server` per thread)\n" ++
  "  --progress N   progress line on stderr every N cases, 0 = never (default 1000)\n" ++
  "exit code 0 only if every case of the whole case list QueenDomSat.enumCases n k was verified"

def parseArgs : List String → Args → Except String Args
  | [], a => pure a
  | "--version" :: r, a => parseArgs r { a with version := true }
  | "--decompress-server" :: r, a => parseArgs r { a with serve := true }
  | "--direct-zstd" :: r, a => parseArgs r { a with direct := true }
  | "--jobs" :: v :: r, a =>
    match v.toNat? with
    | some j => if j == 0 then throw "--jobs must be positive" else parseArgs r { a with jobs := j }
    | none => throw "--jobs needs a number"
  | "--limit" :: v :: r, a =>
    match v.toNat? with
    | some m => parseArgs r { a with limit := some m }
    | none => throw "--limit needs a number"
  | "--chunk-mib" :: v :: r, a =>
    match v.toNat? with
    | some m => if m == 0 then throw "--chunk-mib must be positive" else parseArgs r { a with chunkBytes := m * 1024 * 1024 }
    | none => throw "--chunk-mib needs a number"
  | "--chunk-bytes" :: v :: r, a =>
    match v.toNat? with
    | some m => if m == 0 then throw "--chunk-bytes must be positive" else parseArgs r { a with chunkBytes := m }
    | none => throw "--chunk-bytes needs a number"
  | "--progress" :: v :: r, a =>
    match v.toNat? with
    | some m => parseArgs r { a with progress := m }
    | none => throw "--progress needs a number"
  | "--log" :: v :: r, a => parseArgs r { a with log := some v }
  | "--cases" :: v :: r, a => parseArgs r { a with casesFile := some v }
  | "--zstd" :: v :: r, a => parseArgs r { a with zstd := v }
  | f :: r, a =>
    if f.startsWith "--" then throw s!"unknown or incomplete option {f}"
    else parseArgs r { a with pos := a.pos.push f }

/-- The natural numbers on a line (maximal runs of digits; everything else separates), or an error
if the line contains anything but digits, blanks, commas and square brackets. -/
def lineNats (line : String) : Except String (List Nat) := do
  let mut out : Array Nat := #[]
  let mut cur : Option Nat := none
  for ch in line.toList do
    if ch.isDigit then
      cur := some (cur.getD 0 * 10 + (ch.toNat - '0'.toNat))
    else if ch == ' ' || ch == '\t' || ch == '\r' || ch == ',' || ch == '[' || ch == ']' then
      if let some v := cur then out := out.push v
      cur := none
    else throw s!"unexpected character `{ch}`"
  if let some v := cur then out := out.push v
  return out.toList

/-- The cases of a `--cases` file: 8 integers `ml mr mb mt dR dC dT dS` per line (also accepted:
a JSON list per line, as in the files of `run_cases48.py --cases`). -/
def readCases (file : String) : IO (Except String (List CaseT)) := do
  let text ← IO.FS.readFile file
  let mut out : Array CaseT := #[]
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    match lineNats line with
    | .error e => return .error s!"{file}:{lineNo}: {e}"
    | .ok [] => pure ()
    | .ok [ml, mr, mb, mt, dR, dC, dT, dS] => out := out.push ⟨ml, mr, mb, mt, dR, dC, dT, dS⟩
    | .ok _ => return .error s!"{file}:{lineNo}: expected 8 integers"
  return .ok out.toList

/-- milliseconds as seconds with three decimals -/
def secs (ms : Nat) : String :=
  let frac := toString (ms % 1000)
  s!"{ms / 1000}." ++ String.ofList (List.replicate (3 - frac.length) '0') ++ frac

def reportLines (rep : Report) : List String :=
  [ s!"c result: cases={rep.cases} verified={rep.verified} failed={rep.failed} zstd_warnings={rep.zstdWarnings}",
    s!"c proofs: lrat_bytes={rep.lratBytes} zst_bytes={rep.zstBytes} lemmas={rep.lemmas} hints={rep.hints} base_formulas_built={rep.baseBuilds}",
    s!"c time: wall_s={secs rep.wallMs} worker_cpu_s={secs rep.workerCpuMs} process_cpu_s={secs rep.processCpuMs} decompress_cpu_s={secs rep.childCpuMs} peak_rss_kb={rep.peakRssKb}" ]

/-- The summary line of the log.  `allVerified` and `statement` are passed by the caller, who knows
what has been proved. -/
def summaryJson (rep : Report) (mode : String) (listCases : Nat) (allVerified : Bool)
    (statement : String) : String :=
  "{\"summary\":{" ++
    s!"\"n\":{rep.n},\"k\":{rep.k},\"jobs\":{rep.jobs},\"mode\":\"{mode}\",\"case_list\":{listCases}" ++
    s!",\"cases\":{rep.cases},\"verified\":{rep.verified},\"failed\":{rep.failed}" ++
    s!",\"all_verified\":{allVerified},\"statement\":\"{jsonEscape statement}\"" ++
    s!",\"zstd_warnings\":{rep.zstdWarnings},\"lrat_bytes\":{rep.lratBytes},\"zst_bytes\":{rep.zstBytes}" ++
    s!",\"lemmas\":{rep.lemmas},\"hints\":{rep.hints},\"base_formulas_built\":{rep.baseBuilds}" ++
    s!",\"worker_cpu_ms\":{rep.workerCpuMs},\"process_cpu_ms\":{rep.processCpuMs},\"decompress_cpu_ms\":{rep.childCpuMs}" ++
    s!",\"wall_ms\":{rep.wallMs},\"peak_rss_kb\":{rep.peakRssKb},\"lean\":\"{jsonEscape Lean.versionString}\"" ++
    "}}\n"

def appendLog (log : Option String) (line : String) : IO Unit := do
  if let some f := log then
    let h ← IO.FS.Handle.mk f .append
    h.putStr line
    h.flush

/-- A comment line `c ...` of the standard output.  In a run `qdcheck n k CERTDIR ...` everything that may
contain text given from outside (a path of the command line, an error message of the operating system
or of `zstd`) is written to the standard output through `oneLineStr`, so that such text cannot produce a
line that starts with `s `: the status lines are written only by the four branches at the end of
`main`, from numerals. -/
def comment (s : String) : IO Unit := IO.println ("c " ++ oneLineStr s)

def printFailures (rep : Report) : IO Unit := do
  for (cs, why) in rep.failures do
    comment s!"failed: {cs.tag}: {why}"
  if rep.failed > rep.failures.size then
    comment s!"failed: ... and {rep.failed - rep.failures.size} more (see the log)"

def main (argv : List String) : IO UInt32 := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => IO.eprintln s!"{e}\n{usage}"; return 2
  if args.version then
    IO.println s!"qdcheck (QueenDomCheck 0.1.0), Lean {Lean.versionString}"
    return 0
  if args.serve then
    -- internal: the decompression server of a worker thread (see QueenDomCheck/Decompress.lean)
    -- it copies the decompressed bytes to its standard output, so it must not look like a run of the
    -- checker: no positional arguments, and never the exit code 0
    if !args.pos.isEmpty then IO.eprintln usage; return 2
    serve args.zstd args.chunkBytes.toUSize
    return 4
  if args.pos.size != 3 || (args.limit.isSome && args.casesFile.isSome) then
    IO.eprintln usage; return 2
  let some n := args.pos[0]!.toNat? | do IO.eprintln usage; return 2
  let some k := args.pos[1]!.toNat? | do IO.eprintln usage; return 2
  let certDir : System.FilePath := args.pos[2]!
  let self ← IO.appPath
  let opts : Options := {
    log := args.log.map fun f => (f : System.FilePath)
    chunk := args.chunkBytes.toUSize
    zstd := args.zstd
    server :=
      if args.direct then none
      else some (self.toString,
        #["--decompress-server", "--zstd", args.zstd, "--chunk-bytes", toString args.chunkBytes])
    progressEvery := args.progress }
  let listCases := (enumCases n k).length
  comment s!"qdcheck n={n} k={k} certdir={certDir} jobs={args.jobs} lean={Lean.versionString}"
  comment s!"case list: QueenDomSat.enumCases {n} {k}, {listCases} cases"
  (← IO.getStdout).flush
  -- a subset: the statement about the whole list is never claimed
  let subset : Option (String × List CaseT) ←
    match args.limit, args.casesFile with
    | some m, _ => pure (some (s!"limit {m}", (enumCases n k).take m))
    | none, some f =>
      match ← readCases f with
      | .ok l => pure (some (s!"cases {f}", l))
      | .error e => IO.eprintln s!"qdcheck: {e}"; return 2
    | none, none => pure none
  match subset with
  | some (what, l) =>
    let inList := (l.filter fun cs => decide (CanonAdm n k cs)).length
    comment s!"subset (--{what}): {l.length} cases, {inList} of them in the case list"
    (← IO.getStdout).flush
    let (rep, r) ← verifyList n k l certDir args.jobs opts
    for line in reportLines rep do IO.println (oneLineStr line)
    printFailures rep
    match r with
    | some _ =>
      appendLog args.log (summaryJson rep "subset" listCases false
        s!"forall cs in the {l.length} cases of the subset, (QueenDomSat.caseFormula {n} {k} cs).Unsat")
      IO.println s!"s SUBSET VERIFIED n={n} k={k} cases={l.length} of {listCases} (subset only: not the statement about the whole case list)"
      return 3
    | none =>
      appendLog args.log (summaryJson rep "subset" listCases false "none")
      IO.println s!"s NOT VERIFIED n={n} k={k} verified={rep.verified} failed={rep.failed} (subset of {l.length} cases)"
      return 1
  | none =>
    let (rep, r) ← verifyAllReport n k certDir args.jobs opts
    for line in reportLines rep do IO.println (oneLineStr line)
    printFailures rep
    match r with
    | .ok (_ : PLift (∀ cs ∈ QueenDomSat.enumCases n k, (QueenDomSat.caseFormula n k cs).Unsat)) =>
      -- only here: a value of the type of the hypothesis of the final theorem has been received
      appendLog args.log (summaryJson rep "all" listCases true
        s!"forall cs in QueenDomSat.enumCases {n} {k}, (QueenDomSat.caseFormula {n} {k} cs).Unsat")
      IO.println s!"s ALL VERIFIED n={n} k={k} cases={listCases}"
      return 0
    | .error e =>
      appendLog args.log (summaryJson rep "all" listCases false "none")
      comment e
      IO.println s!"s NOT VERIFIED n={n} k={k} verified={rep.verified} failed={rep.failed} cases={listCases}"
      return 1
