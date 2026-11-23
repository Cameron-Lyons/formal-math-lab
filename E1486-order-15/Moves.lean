import Normalize
import LabelMoves

namespace E1486

private def preserves (k j : Nat) (s : Vertex → Vertex) : Prop :=
  ∀ a, s (s a) = a ∧ ((s a).val < k ↔ a.val < k) ∧
    (a.val < k → s (Fin.ofNat 15 (partner j a.val)) = Fin.ofNat 15 (partner j (s a).val))

private instance (k j : Nat) (s : Vertex → Vertex) : Decidable (preserves k j s) := by
  unfold preserves; infer_instance

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem all_square_moves : ∀ k j : Fin 16, j.val ≤ k.val → (k.val-j.val)%2=0 →
    (Encoding.sqMoves k.val j.val).all (fun h => decide (preserves k.val j.val
      (Encoding.perm h.1 h.2.1 h.2.2))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem all_other_moves : ∀ (k j : Fin 16) (a : Vertex), j.val ≤ k.val →
    (k.val-j.val)%2=0 → k.val ≤ a.val → a.val+1 < 15 →
      preserves k.val j.val (Encoding.swap a (a+1)) := by decide +kernel

private theorem sqPreserves {m k j} (D : DiagNormal m k j) {h} (hh : h ∈ Encoding.sqMoves k j) :
    preserves k j (Encoding.perm h.1 h.2.1 h.2.2) := by
  have e := all_square_moves ⟨k,by have := D.le_size;omega⟩
    ⟨j,by have := D.le_squares;have := D.le_size;omega⟩ D.le_squares D.parity
  exact of_decide_eq_true ((List.all_eq_true.mp e) h hh)

private def mkLabel {k j} (s : Vertex → Vertex) (h : preserves k j s) : Label where
  old := s
  idx := s
  old_idx x := (h x).1
  idx_old x := (h x).1

private theorem preserve_normal {m k j} (D : DiagNormal m k j) (s : Vertex → Vertex)
    (H : preserves k j s) : DiagNormal ((mkLabel s H).pull m) k j := by
  let p := mkLabel s H
  refine ⟨D.le_size,D.le_squares,D.parity,?_,?_⟩
  · intro a; exact ((p.isSq m a).trans (D.sq_iff (s a))).trans (H a).2.1
  · intro a ha
    have sq (x : Vertex) (hx : x.val < k) : Fin.ofNat 15 (partner j x.val) = square m x := by
      rw [← D.diagram x hx]; exact Fin.ext (Nat.mod_eq_of_lt (square m x).isLt)
    have conjugate := (H a).2.2 ha
    rw [sq a ha,sq (s a) ((H a).2.1.mpr ha)] at conjugate
    change (s (square m (s a))).val = _
    rw [← conjugate,(H _).1,D.diagram a ha]

def sqLabel {m k j} (D : DiagNormal m k j) {h} (hh : h ∈ Encoding.sqMoves k j) : Label :=
  mkLabel (Encoding.perm h.1 h.2.1 h.2.2) (sqPreserves D hh)

theorem sqLabel_normal {m k j} (D : DiagNormal m k j) {h} (hh : h ∈ Encoding.sqMoves k j) :
    DiagNormal ((sqLabel D hh).pull m) k j := preserve_normal D _ _

private theorem nsPreserves {m k j} (D : DiagNormal m k j) (a : Vertex)
    (lo : k ≤ a.val) (hi : a.val+1 < 15) : preserves k j (Encoding.swap a (a+1)) := by
  exact all_other_moves ⟨k,by have := D.le_size;omega⟩
    ⟨j,by have := D.le_squares;have := D.le_size;omega⟩ a D.le_squares D.parity lo hi

def nsLabel {m k j} (D : DiagNormal m k j) (a : Vertex)
    (lo : k ≤ a.val) (hi : a.val+1 < 15) : Label :=
  mkLabel (Encoding.swap a (a+1)) (nsPreserves D a lo hi)

theorem nsLabel_normal {m k j} (D : DiagNormal m k j) (a : Vertex)
    (lo : k ≤ a.val) (hi : a.val+1 < 15) :
    DiagNormal ((nsLabel D a lo hi).pull m) k j := preserve_normal D _ _

end E1486
