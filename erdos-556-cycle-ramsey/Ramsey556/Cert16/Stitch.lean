import Ramsey556.Cert16.Tables
import Ramsey556.Dense16Model

namespace Ramsey556.Cert16

/-- Each 16-bit integer gives the two sides of a bipartition of the
corresponding terminal graph, in its stored vertex order. -/
private def cutMasks : Vector Nat 30 := #v[
  21845,21845,10922,21845,10922,21845,10922,21845,10922,21845,
  21845,10922,10922,21845,21845,10922,10922,21845,21845,21845,
  21845,21845,10922,10922,21845,27306,5461,27306,2730,21845]

private theorem terminalSize : (table 16).size = 30 := by decide +kernel

private def cut (i : Fin 30) (v : Fin 16) : Bool := cutMasks[i].testBit v.val

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem terminalCuts : ∀ (i : Fin 30) (a b : Fin 16),
    edge ((table 16).get i.val) a.val b.val = true → cut i a ≠ cut i b := by
  decide +kernel

/-- Assemble the 15 extension layers and check every terminal graph's cut. -/
theorem catalog_of_layers
    (layers : ∀ n, 1 ≤ n → n < 16 →
      ∀ i, i < (table n).size → RowGood n ((table n).get i) (table (n+1))) :
    CatalogProof (fun n => (table n).graphs) where
  start := by decide +kernel
  step := by
    intro n g m lo hi member mask dense safe
    obtain ⟨i,range,rfl⟩ := List.mem_map.mp member
    exact layers n lo hi i (List.mem_range.mp range) m mask dense safe
  final := by
    intro g member
    obtain ⟨i,range,rfl⟩ := List.mem_map.mp member
    have hi := List.mem_range.mp range
    rw [terminalSize] at hi
    exact ⟨cut ⟨i,hi⟩, terminalCuts ⟨i,hi⟩⟩

end Ramsey556.Cert16
