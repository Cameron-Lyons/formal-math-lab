import Std

namespace Height14

/-- Zero-based column and row of a square. -/
abbrev Cell := Nat × Nat

def Adjacent (p q : Cell) : Prop :=
  (p.1 = q.1 ∧ (p.2 + 1 = q.2 ∨ q.2 + 1 = p.2)) ∨
  (p.2 = q.2 ∧ (p.1 + 1 = q.1 ∨ q.1 + 1 = p.1))

instance (p q : Cell) : Decidable (Adjacent p q) := by unfold Adjacent; infer_instance

def Apart (p q : Cell) : Prop := p ≠ q ∧ ¬Adjacent p q

instance (p q : Cell) : Decidable (Apart p q) := by unfold Apart; infer_instance

/-- Starting at p, the successor touches p and all later squares are distinct
from p and do not touch it. Applying the same rule at every square describes
exactly an ordered induced path. -/
def ValidFrom (p : Cell) : List Cell → Prop
  | [] => True
  | q :: qs => Adjacent p q ∧ (∀ z ∈ qs, Apart p z) ∧ ValidFrom q qs

def Induced : List Cell → Prop
  | [] => True
  | p :: ps => ValidFrom p ps

structure Snake (width : Nat) (cells : List Cell) : Prop where
  nonempty : cells ≠ []
  inside : ∀ p ∈ cells, p.1 < width ∧ p.2 < 14
  induced : Induced cells

private theorem Adjacent.ne {p q : Cell} (h : Adjacent p q) : p ≠ q := by
  rintro rfl
  unfold Adjacent at h
  omega

theorem Snake.nodup {width : Nat} {cells : List Cell} (s : Snake width cells) : cells.Nodup := by
  have aux : ∀ (xs : List Cell), Induced xs → xs.Nodup := by
    intro xs
    induction xs with
    | nil => simp
    | cons x rest ih =>
      cases rest with
      | nil => simp
      | cons y ys =>
        rintro ⟨hadj, hfar, hrest⟩
        refine List.nodup_cons.mpr ⟨?_, ih hrest⟩
        intro hx
        rcases List.mem_cons.mp hx with h | h
        · exact hadj.ne h
        · exact (hfar _ h).1 rfl
  exact aux cells s.induced

theorem Snake.pair {width : Nat} {cells : List Cell} (s : Snake width cells)
    (i j : Nat) (hij : i < j) (hj : j < cells.length) :
    Adjacent cells[i] cells[j] ↔ i + 1 = j := by
  have aux (xs : List Cell) (hs : Induced xs) (i j : Nat) (hij : i < j)
      (hj : j < xs.length) : Adjacent xs[i] xs[j] ↔ i + 1 = j := by
    induction xs generalizing i j with
    | nil => simp at hj
    | cons x xs ih =>
      cases j with
      | zero => omega
      | succ j =>
        cases xs with
        | nil => simp at hj
        | cons y ys =>
          obtain ⟨ha, hf, hr⟩ := hs
          cases i with
          | zero =>
            cases j with
            | zero => exact iff_of_true ha rfl
            | succ j =>
              have hj' : j < ys.length := by simpa using hj
              have hmem : ys[j] ∈ ys := List.getElem_mem ..
              exact iff_of_false (hf _ hmem).2 (by omega)
          | succ i =>
            have hh := ih hr i j (by omega) (by simpa using hj)
            simpa only [List.getElem_cons_succ, Nat.succ.injEq] using hh
  exact aux cells s.induced i j hij hj

end Height14
