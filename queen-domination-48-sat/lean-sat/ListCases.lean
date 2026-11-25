import QueenDomSat
/-! `listcases n k`: print the case list `QueenDomSat.enumCases n k` (= `geom.cases_by_frame(n, k)`), one
case per line as eight space-separated integers `ml mr mb mt dR dC dT dS`. -/
open QueenDomSat

def main (args : List String) : IO UInt32 := do
  match args.map String.toNat? with
  | [some n, some k] =>
    let out ← IO.getStdout
    for cs in enumCases n k do
      out.putStrLn (" ".intercalate (cs.toList.map fun v => toString v))
    out.flush
    return 0
  | _ =>
    IO.eprintln "usage: listcases n k"
    return 2
