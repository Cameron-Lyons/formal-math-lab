import Simple.Graph
import Simple.Pack
import Normalize

namespace E1486.Simple
open Finite

private theorem read_row (G : Vertex → Vertex → Prop) (a b : Vertex) :
    (row (pack G) a.val).getLsbD b.val = true ↔ G a b := by
  simp only [row, BitVec.getLsbD_extractLsb', b.isLt, decide_true, Bool.true_and, pack_get]

private theorem nonzero (s : Mask) : s ≠ 0 ↔ ∃ i : Vertex, s.getLsbD i.val = true := by
  classical
  constructor
  · intro h
    apply Classical.byContradiction
    intro hno
    apply h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hn : ¬s.getLsbD i = true := fun h => hno ⟨⟨i,hi⟩,h⟩
    simpa using hn
  · rintro ⟨i,hi⟩ rfl
    simp at hi

private theorem first_bits (k : Fin 16) (i : Vertex) :
    (BitVec.ofNat 15 (2^k.val-1)).getLsbD i.val = true ↔ i.val < k.val := by
  revert k i; decide

private theorem partner_bit (j : Fin 16) (a i : Vertex) :
    (one j.val a.val).getLsbD i.val = true ↔ i.val = Finite.partner j.val a.val := by
  revert j a i; decide

/-- In a normalized square, the sole midpoint on its closed walk is its own square. -/
private theorem closed {m : Operation} (h : Law m) {k j} (n : DiagNormal m k j) (a i : Vertex) :
    Walk (arrows m) a i a ↔ a.val < k ∧ i.val = Finite.partner j a.val := by
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

theorem check_of_law {m : Operation} (h : Law m) {k j} (n : DiagNormal m k j) :
    check k j (pack (arrows m)) (pack (fun a b => arrows m b a)) = true := by
  classical
  let E := arrows m
  let O := fun a : Vertex => row (pack E) a.val
  let I := fun a : Vertex => row (pack (fun a b => E b a)) a.val
  have hout (a y : Vertex) : (O a).getLsbD y.val = true ↔ E a y := read_row E a y
  have hin (a y : Vertex) : (I a).getLsbD y.val = true ↔ E y a := read_row _ a y
  have sm := first_bits (⟨k,by have := n.le_size; omega⟩ : Fin 16)
  have pm := partner_bit (⟨j,by have := n.le_size; have := n.le_squares; omega⟩ : Fin 16)
  have H := fromLaw h
  have pa (a : Vertex) : (I a &&& BitVec.ofNat 15 (2^k-1)) ≠ 0 := by
    obtain ⟨q,mq,e⟩ := H.parent a
    apply (nonzero _).mpr
    refine ⟨q, ?_⟩
    rw [BitVec.getLsbD_and, Bool.and_eq_true]
    exact ⟨(hin _ _).mpr e,(sm _).mpr ((n.sq_iff _).mp ((marked_iff_square h _).mp mq))⟩
  have diag (a : Vertex) : I a &&& O a = (if a.val < k then one j a.val else 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro v hv
    let i : Vertex := ⟨v,hv⟩
    apply Bool.eq_iff_iff.mpr
    change (I a &&& O a).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_and, Bool.and_eq_true, hin, hout, and_comm]
    by_cases ha : a.val < k
    · simp only [ha, ite_true]
      exact (closed h n a i).trans (by simp only [ha, true_and]; exact (pm a i).symm)
    · simp only [ha, ite_false]
      exact (closed h n a i).trans (by simp [ha])
  have reach (a q : Vertex) (hq : q.val < k) : O a &&& I q ≠ 0 := by
    obtain ⟨i,hw⟩ := H.reach a q ((marked_iff_square h q).mpr ((n.sq_iff q).mpr hq))
    exact (nonzero _).mpr ⟨i, by rw [BitVec.getLsbD_and,Bool.and_eq_true]; exact ⟨(hout _ _).mpr hw.1,(hin _ _).mpr hw.2⟩⟩
  have disj (a b : Vertex) (hb : b.val < a.val) : I a &&& I b = 0 ∨ O a &&& O b = 0 := by
    apply Classical.or_iff_not_imp_left.mpr
    intro hi
    apply Classical.byContradiction
    intro ho
    obtain ⟨x,hx⟩ := (nonzero _).mp hi
    obtain ⟨y,hy⟩ := (nonzero _).mp ho
    simp only [BitVec.getLsbD_and,Bool.and_eq_true,hin,hout] at hx hy
    have he := H.unique (show Walk E x a y from ⟨hx.1,hy.1⟩) ⟨hx.2,hy.2⟩
    exact (Nat.ne_of_lt hb) (congrArg Fin.val he.symm)
  simp only [check, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    bne_iff_ne, Bool.or_eq_true]
  intro a ha
  let v : Vertex := ⟨a,ha⟩
  refine ⟨⟨⟨⟨?_,pa v⟩,diag v⟩,?_⟩,?_⟩
  · intro b hb
    let w : Vertex := ⟨b,hb⟩
    exact Bool.eq_iff_iff.mpr ((pack_get E v w).trans (pack_get (fun a b => E b a) w v).symm)
  · intro q hq
    exact reach v ⟨q,by have := n.le_size;omega⟩ hq
  · intro b hb
    exact disj v ⟨b,by omega⟩ hb

end E1486.Simple
