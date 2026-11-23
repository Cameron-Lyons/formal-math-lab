import Ramsey556.CriticalTemplates

namespace Ramsey556

/-- The two cliques have orders eight and seven. All the edges joining them
have the opposite color, except for a star of size `t` centered at vertex 7. -/
def template15 (t : Fin 8) (i j : Fin 15) : Bool :=
  decide ((i.val < 8 ↔ j.val < 8) ∨
    (i.val = 7 ∧ 8 ≤ j.val ∧ j.val < 8 + t.val) ∨
    (j.val = 7 ∧ 8 ≤ i.val ∧ i.val < 8 + t.val))

namespace Fifteen

private def witnesses : Vector (CriticalTemplates.Witness (Fin 8)) 48 := #v[
⟨false,true,7,0xedcba9876543210⟩,
  ⟨false,true,6,0xedcba9876543210⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3ea29180⟩,
  ⟨false,true,5,0xedcba9876543210⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xed3a29180⟩,
  ⟨true,false,0,0xed3a29180⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3ea29180⟩,
  ⟨true,false,0,0xed3a29180⟩,
  ⟨false,true,4,0xedcba9876543210⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3ea29180⟩,
  ⟨true,false,0,0xa39281e70⟩,
  ⟨true,false,0,0xb3a291e80⟩,
  ⟨true,false,0,0xa39281e70⟩,
  ⟨true,false,0,0xb3a2e9180⟩,
  ⟨true,false,0,0xb3a291870⟩,
  ⟨true,false,0,0xb3a291870⟩,
  ⟨true,false,0,0xb3a291870⟩,
  ⟨true,false,0,0xa39281e70⟩,
  ⟨true,false,0,0xa392e8170⟩,
  ⟨true,false,0,0xb3a291860⟩,
  ⟨true,false,0,0xb3a291860⟩,
  ⟨true,false,0,0xb3a291860⟩,
  ⟨true,false,0,0xb3a291860⟩,
  ⟨false,false,0,0xdb97531eca86420⟩,
  ⟨false,false,1,0xdb97531eca86420⟩,
  ⟨false,false,2,0xdb97531eca86420⟩,
  ⟨false,false,3,0xdb97531eca86420⟩,
  ⟨true,false,0,0xd1ea86420⟩,
  ⟨true,false,0,0xeb97531d0⟩,
  ⟨true,false,0,0xd1ea86420⟩,
  ⟨true,false,0,0xd97531e20⟩,
  ⟨true,false,0,0xedca86420⟩,
  ⟨true,false,0,0xe4dca8620⟩,
  ⟨true,false,0,0xedca86420⟩,
  ⟨true,false,0,0xd1ca86420⟩,
  ⟨true,false,0,0xd1ca86420⟩]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem verified_all : ∀ i : Fin 48, CriticalTemplates.Verified (by decide) template15
    ((Cert16.table 15).get i.val) witnesses[i] := by
  unfold CriticalTemplates.Verified
  decide +kernel

/-- Classification of every two-colored K₁₅ with no monochromatic nine-cycle. -/
theorem classify (c : Coloring 15) (r s : Fin 3) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s)
    (free : ¬ HasMonoC9 c) :
    ∃ (t : Fin 8) (a b : Fin 3) (v : Fin 15 → Fin 15),
      ((a = r ∧ b = s) ∨ (a = s ∧ b = r)) ∧
      (∀ ⦃i j⦄, v i = v j → i = j) ∧
      ∀ i j, i ≠ j → c.edge (v i) (v j) = if template15 t i j then a else b :=
  CriticalTemplates.classify (by decide) (by decide) witnesses template15 (by decide +kernel) verified_all
    (by decide +kernel) c r s ne uses free

end Fifteen
end Ramsey556
