import Simple.Graph
import Normalize
import Simple.Test

/-! The arrows of a relabeled table pass the finite test. -/

namespace E1486.Test
open E1486.Simple

variable {n : Nat}

/-- Record a relation on the `n` vertices as `n²` bits. -/
noncomputable def pack (G : Fin n → Fin n → Prop) : BitVec (n*n) := by
  classical
  let cells := (List.range (n*n)).map fun i =>
    if h : 0 < n then decide (G ⟨i/n%n, Nat.mod_lt _ h⟩ ⟨i%n, Nat.mod_lt _ h⟩) else false
  exact (BitVec.ofBoolListLE cells).setWidth (n*n)

theorem edge_pack (G : Fin n → Fin n → Prop) (a b : Fin n) :
    edge n (pack G) a.val b.val = true ↔ G a b := by
  classical
  have pos : 0 < n := a.pos
  have bound : n*a.val+b.val < n*n :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left b.isLt _) (Nat.mul_le_mul_left n a.isLt)
  have ea : (⟨(n*a.val+b.val)/n%n, Nat.mod_lt _ pos⟩ : Fin n) = a := Fin.ext (by
    simp [Nat.mul_add_div pos, Nat.div_eq_of_lt b.isLt, Nat.mod_eq_of_lt a.isLt])
  have eb : (⟨(n*a.val+b.val)%n, Nat.mod_lt _ pos⟩ : Fin n) = b := Fin.ext (by
    simp [Nat.mod_eq_of_lt b.isLt])
  unfold edge pack
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range bound]
  simp only [bound, decide_true, Bool.true_and, Option.map_some, Option.getD_some, pos, ↓reduceDIte]
  simp only [ea, eb, decide_eq_true_eq]

example : partner = E1486.partner := rfl

/-- The only closed route through a square `a` is `a → a² → a`. A nonsquare has none. -/
private theorem closed {m : Fin n → Fin n → Fin n} (h : Law m) {k j}
    (d : DiagNormal m k j) (a i : Fin n) :
    Walk (arrows m) a i a ↔ a.val < k ∧ i.val = partner j a.val := by
  have loopAt (ha : Square m a) : Walk (arrows m) a (m a a) a := by
    refine ⟨Or.inl (square_edge ha),Or.inl ?_⟩
    have e := square_edge (show Square m (m a a) from ⟨a,rfl⟩)
    rwa [square_involution h ha] at e
  constructor
  · intro hw
    have hs := (marked_iff_square h a).mp ⟨i,hw⟩
    have ha := (d.sq_iff a).mp hs
    exact ⟨ha, (congrArg Fin.val ((fromLaw h).unique hw (loopAt hs))).trans (d.diagram a ha)⟩
  · rintro ⟨ha,hp⟩
    have e : i = m a a := Fin.ext (hp.trans (d.diagram a ha).symm)
    exact e ▸ loopAt ((d.sq_iff a).mpr ha)

theorem check_of_law {m : Fin n → Fin n → Fin n} (h : Law m) {k j} (d : DiagNormal m k j) :
    check n k j (pack (arrows m)) = true := by
  have rules := fromLaw h
  have arrow (a b : Fin n) : edge n (pack (arrows m)) a.val b.val = true ↔ arrows m a b :=
    edge_pack _ a b
  have marked (q : Fin n) : Marked (arrows m) q ↔ q.val < k :=
    (marked_iff_square h q).trans (d.sq_iff q)
  simp only [check, List.all_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true]
  intro a ha
  let v : Fin n := ⟨a,ha⟩
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · -- 1. The square a² points to a.
    obtain ⟨q,mq,e⟩ := rules.parent v
    exact ⟨q.val, (marked q).mp mq, (arrow q v).mpr e⟩
  · -- 2. Closed routes.
    intro i hi
    let u : Fin n := ⟨i,hi⟩
    apply beq_iff_eq.mpr
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact (and_congr (arrow v u) (arrow u v)).trans (closed h d v u)
  · -- 3. The route a → a⋆q → q.
    intro q hq
    let u : Fin n := ⟨q,by have := d.le_size; omega⟩
    obtain ⟨i,hw⟩ := rules.reach v u ((marked u).mpr hq)
    exact ⟨i.val, i.isLt, (arrow v i).mpr hw.1, (arrow i u).mpr hw.2⟩
  · -- 4. Midpoints are unique.
    intro b hb
    let u : Fin n := ⟨b,by omega⟩
    apply Classical.byContradiction
    intro bad
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false,
      List.any_eq_true, List.mem_range, Bool.and_eq_true] at bad
    obtain ⟨⟨x,hx,xa,xb⟩,⟨y,hy,ay,yb⟩⟩ := bad
    let X : Fin n := ⟨x,hx⟩
    let Y : Fin n := ⟨y,hy⟩
    have same := rules.unique
      (show Walk (arrows m) X v Y from ⟨(arrow X v).mp xa,(arrow v Y).mp ay⟩)
      ⟨(arrow X u).mp xb,(arrow u Y).mp yb⟩
    exact Nat.ne_of_gt hb (congrArg Fin.val same)

end E1486.Test
