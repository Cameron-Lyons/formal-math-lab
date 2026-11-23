import BookRamsey

open BookRamsey

private def readMatrix (path : System.FilePath) (n : Nat) : IO (Graph n) := do
  let lines ← IO.FS.lines path
  if lines.size != n then
    throw <| IO.userError s!"expected {n} rows, got {lines.size}"
  let mut rows := #[]
  for line in lines do
    let chars := line.trimAscii.toString.toList
    if chars.length != n || !chars.all (fun c => c == '0' || c == '1') then
      throw <| IO.userError s!"row {rows.size} must contain {n} binary digits"
    rows := rows.push (chars.map (· == '1')).toArray
  for i in [:n] do
    if rows[i]![i]! then
      throw <| IO.userError s!"loop on the diagonal at {i}"
    for j in [i+1:n] do
      if rows[i]![j]! != rows[j]![i]! then
        throw <| IO.userError s!"asymmetric entries at ({i},{j})"
  return Graph.ofUpper (fun u v => rows[u.val]![v.val]!)

private structure Counts where
  largest : Option (Nat × Nat × Nat) := none
  violating : Nat := 0

private def Counts.record (s : Counts) (k u v pages : Nat) : Counts :=
  let largest := match s.largest with
    | none => some (pages, u, v)
    | some (m, _, _) => if m < pages then some (pages, u, v) else s.largest
  ⟨largest, s.violating + (if k ≤ pages then 1 else 0)⟩

private def Counts.report (s : Counts) (color : String) (k : Nat) : String :=
  let witness := match s.largest with
    | none => "no edges"
    | some (count, u, v) => s!"maximum {count} pages on edge ({u},{v})"
  s!"{color}, {witness}. {s.violating} unordered spines have at least {k} pages."

private def diagnose (g : Graph n) (red blue : Nat) : IO Unit := do
  let mut rs : Counts := {}
  let mut bs : Counts := {}
  let vertices := List.finRange n
  for u in vertices do
    for v in vertices do
      if u < v then
        if g.adj u v then
          rs := rs.record red u.val v.val (g.commonCount u v)
        else
          bs := bs.record blue u.val v.val (g.complement.commonCount u v)
  IO.println (rs.report "red" red)
  IO.println (bs.report "blue" blue)

private def verify (path : String) (n red blue : Nat) : IO UInt32 := do
  let graph ← readMatrix path n
  diagnose graph red blue
  if graph.check red blue then
    IO.println s!"PASS on {n} vertices"
    return 0
  else
    IO.println s!"FAIL on {n} vertices"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => verify path 254 63 64
  | [path, n, red, blue] =>
    if let some (nv, r, b) := (do return (← n.toNat?, ← red.toNat?, ← blue.toNat?)) then
      verify path nv r b
    else
      throw <| IO.userError "expected three natural numbers after the matrix path"
  | _ =>
    IO.eprintln "usage: lake exe verify MATRIX [VERTICES RED_PAGES BLUE_PAGES]"
    return 2
