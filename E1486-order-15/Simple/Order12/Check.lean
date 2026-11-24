import Simple.Graph
import Normalize
import Simple.Order12.Test

/-! The arrows of a relabeled table pass the finite test. -/

namespace E1486.Order12
open E1486.Simple

/-- Record a relation on the 12 vertices as 144 bits. -/
noncomputable def pack (G : Fin 12 → Fin 12 → Prop) : Graph := by
  classical
  let cells := (List.range 144).map fun i =>
    decide (G (Fin.ofNat 12 (i / 12)) (Fin.ofNat 12 (i % 12)))
  exact (BitVec.ofBoolListLE cells).setWidth 144

theorem edge_pack (G : Fin 12 → Fin 12 → Prop) (a b : Fin 12) :
    edge (pack G) a.val b.val = true ↔ G a b := by
  classical
  have bound : 12*a.val+b.val < 144 := by omega
  have ea : Fin.ofNat 12 ((12*a.val+b.val)/12) = a := Fin.ext (by
    simp [Fin.ofNat] <;> omega)
  have eb : Fin.ofNat 12 ((12*a.val+b.val)%12) = b := Fin.ext (by
    simp [Fin.ofNat] <;> omega)
  unfold edge pack
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range]
  simp only [bound, decide_true, Bool.true_and, Option.map_some, Option.getD_some]
  simp only [ea,eb,decide_eq_true_eq]
  exact bound

example : partner = E1486.partner := rfl

/-- The only closed route through a square `a` is `a → a² → a`. A nonsquare has none. -/
private theorem closed {m : Fin 12 → Fin 12 → Fin 12} (h : Law m) {k j}
    (n : DiagNormal m k j) (a i : Fin 12) :
    Walk (arrows m) a i a ↔ a.val < k ∧ i.val = partner j a.val := by
  have loopAt (ha : Square m a) : Walk (arrows m) a (m a a) a := by
    refine ⟨Or.inl (square_edge ha),Or.inl ?_⟩
    have e := square_edge (show Square m (m a a) from ⟨a,rfl⟩)
    rwa [square_involution h ha] at e
  constructor
  · intro hw
    have hs := (marked_iff_square h a).mp ⟨i,hw⟩
    have ha := (n.sq_iff a).mp hs
    exact ⟨ha, (congrArg Fin.val ((fromLaw h).unique hw (loopAt hs))).trans (n.diagram a ha)⟩
  · rintro ⟨ha,hp⟩
    have e : i = m a a := Fin.ext (hp.trans (n.diagram a ha).symm)
    exact e ▸ loopAt ((n.sq_iff a).mpr ha)

theorem check_of_law {m : Fin 12 → Fin 12 → Fin 12} (h : Law m) {k j} (n : DiagNormal m k j) :
    check k j (pack (arrows m)) = true := by
  have rules := fromLaw h
  have arrow (a b : Fin 12) : edge (pack (arrows m)) a.val b.val = true ↔ arrows m a b :=
    edge_pack _ a b
  have marked (q : Fin 12) : Marked (arrows m) q ↔ q.val < k :=
    (marked_iff_square h q).trans (n.sq_iff q)
  simp only [check, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  intro a ha
  let v : Fin 12 := ⟨a,ha⟩
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · -- 1. The square a² points to a.
    obtain ⟨q,mq,e⟩ := rules.parent v
    exact ⟨q.val, (marked q).mp mq, (arrow q v).mpr e⟩
  · -- 2. Closed routes.
    intro i hi
    let w : Fin 12 := ⟨i,hi⟩
    apply beq_iff_eq.mpr
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact (and_congr (arrow v w) (arrow w v)).trans (closed h n v w)
  · -- 3. The route a → a⋆q → q.
    intro q hq
    let w : Fin 12 := ⟨q,by have := n.le_size; omega⟩
    obtain ⟨i,hw⟩ := rules.reach v w ((marked w).mpr hq)
    exact ⟨i.val, i.isLt, (arrow v i).mpr hw.1, (arrow i w).mpr hw.2⟩
  · -- 4. Midpoints are unique.
    intro b hb
    let w : Fin 12 := ⟨b,by omega⟩
    apply Classical.byContradiction
    intro bad
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
      List.any_eq_true, List.mem_range, Bool.and_eq_true] at bad
    obtain ⟨⟨x,hx,xa,xb⟩,⟨y,hy,ay,yb⟩⟩ := bad
    let X : Fin 12 := ⟨x,hx⟩
    let Y : Fin 12 := ⟨y,hy⟩
    have same := rules.unique
      (show Walk (arrows m) X v Y from ⟨(arrow X v).mp xa,(arrow v Y).mp ay⟩)
      ⟨(arrow X w).mp xb,(arrow w Y).mp yb⟩
    exact Nat.ne_of_gt hb (congrArg Fin.val same)

end E1486.Order12
