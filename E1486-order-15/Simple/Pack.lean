import Simple.FiniteBase

namespace E1486.Simple

noncomputable def pack (G : Fin 15 → Fin 15 → Prop) : BitVec 225 := by
  classical
  let cells := (List.range 225).map fun i =>
    decide (G (Fin.ofNat 15 (i / 15)) (Fin.ofNat 15 (i % 15)))
  exact (BitVec.ofBoolListLE cells).setWidth 225

theorem pack_get (G : Fin 15 → Fin 15 → Prop) (a b : Fin 15) :
    (pack G).getLsbD (15*a.val+b.val) = true ↔ G a b := by
  classical
  have bound : 15*a.val+b.val < 225 := by omega
  have ea : Fin.ofNat 15 ((15*a.val+b.val)/15) = a := Fin.ext (by
    simp [Fin.ofNat] <;> omega)
  have eb : Fin.ofNat 15 ((15*a.val+b.val)%15) = b := Fin.ext (by
    simp [Fin.ofNat] <;> omega)
  unfold pack
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range]
  simp only [bound, decide_true, Bool.true_and, Option.map_some, Option.getD_some]
  simp only [ea,eb,decide_eq_true_eq]
  exact bound

end E1486.Simple
