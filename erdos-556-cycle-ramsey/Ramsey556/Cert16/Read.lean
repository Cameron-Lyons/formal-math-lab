import Lean
import Ramsey556.Cert16.Check

/-! This elaborator translates the binary certificate to ordinary constructor
expressions and natural literals. All mathematical checks happen in the kernel. -/

namespace Ramsey556.Cert16
open Lean Elab Term

private abbrev Parser := StateT Nat IO

/-- Fields in the file are unsigned, little endian. -/
private def readLE (bytes : ByteArray) (width : Nat) : Parser Nat := do
  let pos ← get
  if pos + width > bytes.size then throw (IO.userError "truncated graph certificate")
  let mut value := 0
  for j in [:width] do
    value := value ||| (bytes[pos+j]!.toNat <<< (8*j))
  set (pos+width)
  return value

private def rows (bytes : ByteArray) (count : Nat) : Parser Expr := do
  let mut result := #[]
  for _ in [:count] do
    let g ← readLE bytes 16
    let pathCount ← readLE bytes 2
    let mut ps := #[]
    let mut matrix := 0
    for _ in [:pathCount] do
      let c ← readLE bytes 4
      ps := ps.push (mkNatLit c)
      matrix := matrix ||| (1 <<< (16 * (c >>> 28) + c % 16))
    let moveCount ← readLE bytes 4
    let mut ms := #[]
    let mut hits := 0
    for _ in [:moveCount] do
      let mask ← readLE bytes 2
      let index ← readLE bytes 2
      let h ← readLE bytes 16
      let perm ← readLE bytes 8
      ms := ms.push (mkApp4 (mkConst ``Move.mk) (mkNatLit mask) (mkNatLit index) (mkNatLit h) (mkNatLit perm))
      hits := hits ||| (1 <<< mask)
    let mkList (ty : Expr) (xs : Array Expr) := xs.foldr
      (fun x s => mkApp3 (mkConst ``List.cons [.zero]) ty x s) (mkApp (mkConst ``List.nil [.zero]) ty)
    result := result.push (mkApp5 (mkConst ``Row.mk) (mkNatLit g)
      (mkList (mkConst ``Nat) ps) (mkNatLit matrix)
      (mkList (mkConst ``Move) ms) (mkNatLit hits))
  let ty := Lean.mkConst ``Row
  return result.foldr (fun x s => mkApp3 (mkConst ``List.cons [.zero]) ty x s)
    (mkApp (mkConst ``List.nil [.zero]) ty)

syntax "cert16Rows% " str num num : term

elab_rules : term
  | `(cert16Rows% $path:str $pos:num $count:num) => do
    let here := (System.FilePath.mk (← getFileName)).parent.getD "."
    let bytes ← IO.FS.readBinFile (here / path.getString)
    return (← (rows bytes count.getNat).run pos.getNat).1

end Ramsey556.Cert16
