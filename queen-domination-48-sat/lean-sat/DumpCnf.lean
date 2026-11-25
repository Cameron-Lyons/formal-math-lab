import QueenDomSat
import Std.Sat.CNF.Dimacs
import Std.Data.HashMap
/-!
`dumpcnf n k ml mr mb mt dR dC dT dS`
    prints the DIMACS text `QueenDomSat.caseDimacs` of one case to stdout (the text of
    `enc.dimacs(B, *enc.case_extra(B, case))` of `code/frame/enc.py`).
`dumpcnf --batch n k OUTDIR`
    reads cases (8 integers `ml mr mb mt dR dC dT dS` per line) from stdin and writes
    `OUTDIR/<ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS>.cnf` for each; a `Base` is built once per deficit vector.
`dumpcnf --stream n k`
    reads cases from stdin as `--batch` does and writes, for each case, the line
    `c <ml>_<mr>_<mb>_<mt>_<dR>_<dC>_<dT>_<dS> <number of bytes>` followed by the DIMACS text to stdout
    (no files; used by `scripts/compare_enc.py --full` to hash many formulas).
`dumpcnf --std n k ml mr mb mt dR dC dT dS`
    prints `Std.Sat.CNF.dimacs (QueenDomSat.caseFormula n k case)`: the formula `caseCNF B ml mr mb mt` as
    the LRAT checker sees it, printed by the DIMACS printer of `Std` (used by `scripts/compare_enc.py` to
    test `toCNF`).
-/
open QueenDomSat

def parseNats (ws : List String) : Option (List Nat) := ws.mapM String.toNat?

/-- The natural numbers on a line (decimal, separated by white space); `none` if the line contains
anything else. -/
def parseLine (s : String) : Option (List Nat) :=
  go s.toList none []
where
  push (cur : Option Nat) (acc : List Nat) : List Nat :=
    match cur with
    | some v => v :: acc
    | none => acc
  go : List Char → Option Nat → List Nat → Option (List Nat)
    | [], cur, acc => some (push cur acc).reverse
    | ch :: cs, cur, acc =>
      if ch.isDigit then go cs (some (cur.getD 0 * 10 + (ch.toNat - '0'.toNat))) acc
      else if ch.isWhitespace then go cs none (push cur acc)
      else none

def usage : IO UInt32 := do
  IO.eprintln "usage: dumpcnf n k ml mr mb mt dR dC dT dS\n       dumpcnf --batch n k OUTDIR   (cases on stdin, 8 integers per line)\n       dumpcnf --stream n k         (cases on stdin, 8 integers per line)\n       dumpcnf --std n k ml mr mb mt dR dC dT dS"
  return 2

/-- A `Base` together with its DIMACS text. -/
structure BaseText where
  base : Base
  text : String

/-- Read cases from `stdin` until end of file and hand the DIMACS text of each to `emit`; returns the
number of cases, or `none` after a malformed line. -/
partial def batchLoop (n k : Nat) (emit : CaseT → String → IO Unit) (stdin : IO.FS.Stream)
    (cache : Std.HashMap (Nat × Nat × Nat × Nat) BaseText) (count : Nat) : IO (Option Nat) := do
  let line ← stdin.getLine
  if line.isEmpty then
    return some count
  match parseLine line with
    | some [] => batchLoop n k emit stdin cache count
    | some [ml, mr, mb, mt, dR, dC, dT, dS] =>
      let key := (dR, dC, dT, dS)
      let (bt, cache) ← match cache[key]? with
        | some bt => pure (bt, cache)
        | none =>
          let B := mkBase n k dR dC dT dS
          let bt : BaseText := { base := B, text := B.text }
          pure (bt, cache.insert key bt)
      let (extra, nv) := caseExtra bt.base ml mr mb mt
      let cs : CaseT := ⟨ml, mr, mb, mt, dR, dC, dT, dS⟩
      emit cs (dimacsOfText bt.text bt.base.cls.size extra nv)
      batchLoop n k emit stdin cache (count + 1)
    | _ =>
      IO.eprintln s!"dumpcnf: bad case line: {line}"
      return none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", n, k, outDir] =>
    match n.toNat?, k.toNat? with
    | some n, some k =>
      IO.FS.createDirAll outDir
      let emit (cs : CaseT) (txt : String) : IO Unit :=
        IO.FS.writeFile ((outDir : System.FilePath) / (cs.tag ++ ".cnf")) txt
      match ← batchLoop n k emit (← IO.getStdin) {} 0 with
      | some count =>
        IO.eprintln s!"dumpcnf: wrote {count} files"
        return 0
      | none => return 1
    | _, _ => usage
  | ["--stream", n, k] =>
    match n.toNat?, k.toNat? with
    | some n, some k =>
      let out ← IO.getStdout
      let emit (cs : CaseT) (txt : String) : IO Unit := do
        out.putStr s!"c {cs.tag} {txt.utf8ByteSize}\n"
        out.putStr txt
        out.flush
      match ← batchLoop n k emit (← IO.getStdin) {} 0 with
      | some _ => return 0
      | none => return 1
    | _, _ => usage
  | "--std" :: rest =>
    match parseNats rest with
    | some [n, k, ml, mr, mb, mt, dR, dC, dT, dS] =>
      let out ← IO.getStdout
      out.putStr (Std.Sat.CNF.dimacs (caseFormula n k ⟨ml, mr, mb, mt, dR, dC, dT, dS⟩))
      out.flush
      return 0
    | _ => usage
  | _ =>
    match parseNats args with
    | some [n, k, ml, mr, mb, mt, dR, dC, dT, dS] =>
      let out ← IO.getStdout
      out.putStr (caseDimacs n k ⟨ml, mr, mb, mt, dR, dC, dT, dS⟩)
      out.flush
      return 0
    | _ => usage
