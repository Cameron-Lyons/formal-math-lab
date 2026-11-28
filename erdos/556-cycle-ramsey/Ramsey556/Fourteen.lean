import Ramsey556.CriticalTemplates

namespace Ramsey556

/-- The left clique has size eight or seven, the right clique fills the remaining
vertices. The last left vertex may send additional clique-colored edges to the
first vertices of the right clique. -/
def template14 (wide : Bool) (t : Fin 8) (i j : Fin 14) : Bool :=
  let w := if wide then 8 else 7
  decide ((i.val < w ↔ j.val < w) ∨
    (i.val + 1 = w ∧ w ≤ j.val ∧ j.val < w + t.val) ∨
    (j.val + 1 = w ∧ w ≤ i.val ∧ i.val < w + t.val))

namespace Fourteen

private abbrev Shape := Bool × Fin 7
private def shape (x : Shape) := template14 x.1 x.2.castSucc

private def witnesses : Vector (CriticalTemplates.Witness Shape) 81 := #v[
  ⟨false, true, (true, 6), 0xdcba9876543210⟩,
  ⟨false, true, (true, 5), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3da29180⟩,
  ⟨false, true, (true, 4), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xdc3a29180⟩,
  ⟨true, false, (false, 0), 0xdc3a29180⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3da29180⟩,
  ⟨true, false, (false, 0), 0xdc3a29180⟩,
  ⟨false, true, (true, 3), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3da29180⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xb3a291d80⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xa39281c70⟩,
  ⟨true, false, (false, 0), 0xa39281c70⟩,
  ⟨true, false, (false, 0), 0xb3a2d9180⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xb3a291870⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xb4a392870⟩,
  ⟨true, false, (false, 0), 0xb4a392870⟩,
  ⟨false, true, (false, 6), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa3d928170⟩,
  ⟨false, true, (false, 5), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xdc3928170⟩,
  ⟨true, false, (false, 0), 0xdc3928170⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa3d928170⟩,
  ⟨true, false, (false, 0), 0xdc3928170⟩,
  ⟨false, true, (false, 4), 0xdcba9876543210⟩,
  ⟨true, false, (false, 0), 0xa39281d70⟩,
  ⟨true, false, (false, 0), 0xa392d8170⟩,
  ⟨true, false, (false, 0), 0xa3d928170⟩,
  ⟨true, false, (false, 0), 0xb3a291860⟩,
  ⟨true, false, (false, 0), 0xb3a291860⟩,
  ⟨true, false, (false, 0), 0xb3a291860⟩,
  ⟨true, false, (false, 0), 0xb3a291860⟩,
  ⟨true, false, (false, 0), 0xcba987650⟩,
  ⟨false, false, (false, 0), 0xdb97531ca86420⟩,
  ⟨false, false, (false, 1), 0xb97531d0ca8642⟩,
  ⟨false, false, (true, 0), 0xb97531dca86420⟩,
  ⟨false, false, (false, 2), 0xca86420db97531⟩,
  ⟨false, false, (true, 1), 0xb97531dca86420⟩,
  ⟨false, false, (false, 3), 0xca86420db97531⟩,
  ⟨false, false, (true, 2), 0xb97531dca86420⟩,
  ⟨true, false, (false, 0), 0xd1ca86420⟩,
  ⟨true, false, (false, 0), 0xd1ca86420⟩,
  ⟨true, false, (false, 0), 0xd1ca86420⟩,
  ⟨true, false, (false, 0), 0xd31c86420⟩,
  ⟨true, false, (false, 0), 0xd1ca86420⟩,
  ⟨true, false, (false, 0), 0xb1ca86420⟩]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem checked : ∀ i : Fin 81, CriticalTemplates.Verified (by decide) shape
    ((Cert16.table 14).get i.val) witnesses[i] := by
  unfold CriticalTemplates.Verified
  decide +kernel

/-- Any two-colored K₁₄ avoiding a monochromatic C₉ is either two seven-cliques
or an eight-clique and a six-clique in the same color. The exceptional edges
between the two cliques form a star of size at most six. -/
theorem classify (c : Coloring 14) (r s : Fin 3) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s) (free : ¬ HasMonoC9 c) :
    ∃ (wide : Bool) (t : Fin 8) (a b : Fin 3) (v : Fin 14 → Fin 14),
      t.val ≤ 6 ∧ ((a = r ∧ b = s) ∨ (a = s ∧ b = r)) ∧
      Function.Injective v ∧
      ∀ i j, i ≠ j → c.edge (v i) (v j) = if template14 wide t i j then a else b := by
  obtain ⟨⟨w,t⟩,a,b,v,col,inj,edges⟩ := CriticalTemplates.classify (by decide) (by decide)
    witnesses shape (by decide +kernel) checked (by decide +kernel) c r s ne uses free
  exact ⟨w,t.castSucc,a,b,v,Nat.le_of_lt_succ t.isLt,col,@inj,edges⟩

end Fourteen
end Ramsey556
