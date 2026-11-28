import Height14.Path
import Height14.Profile
import Height14.Intervals

namespace Height14
open Interval

/-- Number the grid squares by scanning down each column. -/
def number (c : Cell) : Nat := 14*c.1+c.2

def ForwardEdge (a b : Nat) : Prop := a+14=b ∨ (a+1=b ∧ b%14≠0)
def GridEdge (a b : Nat) : Prop := ForwardEdge a b ∨ ForwardEdge b a

private theorem number_adjacent {a b : Cell} (ha : a.2<14) (hb : b.2<14) :
    GridEdge (number a) (number b) ↔ Adjacent a b := by
  obtain ⟨x,y⟩ := a; obtain ⟨u,v⟩ := b
  simp only [GridEdge, ForwardEdge, number, Adjacent] at *
  omega

structure Ranked (w l : Nat) where
  pos : Fin l → Nat
  nonempty : 0 < l
  bounded : ∀ i, pos i < w*14
  injective : ∀ ⦃i j⦄, pos i = pos j → i = j
  adjacent : ∀ i j, nextTo i j ↔ GridEdge (pos i) (pos j)

def Snake.ranked {w cells} (s : Snake w cells) : Ranked w cells.length where
  pos i := number cells[i.val]
  nonempty := List.length_pos_iff.mpr s.nonempty
  bounded i := by
    obtain ⟨hx,hy⟩ := s.inside cells[i.val] (List.getElem_mem ..)
    simp only [number]; omega
  injective := by
    intro i j hij
    have hi := (s.inside cells[i.val] (List.getElem_mem ..)).2
    have hj := (s.inside cells[j.val] (List.getElem_mem ..)).2
    have equal : cells[i.val] = cells[j.val] := by
      apply Prod.ext <;> unfold number at hij <;> omega
    exact Fin.ext (s.nodup.getElem_inj.mp equal)
  adjacent i j := by
    rw [number_adjacent (s.inside _ (List.getElem_mem ..)).2 (s.inside _ (List.getElem_mem ..)).2]
    by_cases h : i.val < j.val
    · rw [s.pair i.val j.val h j.isLt]; unfold nextTo; omega
    by_cases h' : j.val < i.val
    · have sym : Adjacent cells[i.val] cells[j.val] ↔ Adjacent cells[j.val] cells[i.val] := by
        unfold Adjacent; omega
      rw [sym,s.pair j.val i.val h' i.isLt]; unfold nextTo; omega
    · have eq : i = j := Fin.ext (by omega)
      subst j; unfold Adjacent nextTo; omega

namespace Ranked
variable {w l : Nat} (P : Ranked w l)

def row (t : Nat) : Row := ⟨t%14, Nat.mod_lt _ (by decide)⟩
def upRow (t : Nat) : Row := ⟨t%14-1, by have := Nat.mod_lt t (by decide : 0<14); omega⟩

/-- The occupied square representing a row is one of the last fourteen
positions scanned. There is at most one such square in each row. -/
def At (t : Nat) (r : Row) (i : Fin l) : Prop :=
  P.pos i % 14 = r.val ∧ P.pos i < t ∧ t ≤ P.pos i + 14

def Occ (t : Nat) (r : Row) : Prop := ∃ i, P.At t r i

def Link (t : Nat) (r s : Row) : Prop :=
  ∃ i j, P.At t r i ∧ P.At t s j ∧ joined P.pos t i j

def Saturated (t : Nat) (i : Fin l) : Prop :=
  ∃ j k, j ≠ k ∧ nextTo i j ∧ nextTo i k ∧ P.pos j < t ∧ P.pos k < t

def Sat (t : Nat) (r : Row) : Prop := ∃ i, P.At t r i ∧ P.Saturated t i

def isolatedAt (t : Nat) (i : Fin l) : Prop := ∀ j, nextTo i j → t ≤ P.pos j

def Pivot (t : Nat) : Prop :=
  t%14 ≠ 0 ∧ ∃ i, P.pos i+1=t ∧ P.isolatedAt t i

def Done (t : Nat) : Prop := (∀ i, P.pos i<t) ∧ ¬∃ r, P.Occ t r

noncomputable def bit (p : Prop) : Bool := @decide p (Classical.propDecidable p)
@[simp] theorem bit_true (p : Prop) : bit p = true ↔ p := by classical simp [bit]
@[simp] theorem bit_false (p : Prop) : bit p = false ↔ ¬ p := by classical simp [bit]

noncomputable def profile (t : Nat) : Profile where
  done := bit (P.Done t)
  occ i := bit (P.Occ t i)
  sat i := bit (P.Sat t i)
  linked i j := bit (P.Link t i j)
  isolated := bit (P.Pivot t)

theorem at_unique {t r i j} (hi : P.At t r i) (hj : P.At t r j) : i=j := by
  apply P.injective
  unfold At at *; omega

theorem at_row {t r i} (h : P.At t r i) : r = row (P.pos i) :=
  Fin.ext h.1.symm

theorem at_same {t i} : P.At t (row t) i ↔ P.pos i + 14 = t := by
  unfold At row; simp only; omega

theorem at_above {t i} (hr : t%14 ≠ 0) : P.At t (upRow t) i ↔ P.pos i + 1 = t := by
  unfold At upRow; simp only; omega

theorem at_other {t r i} (hr : r ≠ row t) :
    P.At (t+1) r i ↔ P.At t r i := by
  have : r.val ≠ t%14 := fun e => hr (Fin.ext e)
  unfold At; omega

theorem at_new {t i} : P.At (t+1) (row t) i ↔ P.pos i=t := by
  unfold At row; simp only; omega

theorem older_neighbor {t p i} (hp : P.pos p=t) :
    (nextTo i p ∧ P.pos i<t) ↔ P.At t (row t) i ∨ (t%14 ≠ 0 ∧ P.At t (upRow t) i) := by
  rw [P.adjacent i p,hp,P.at_same]
  by_cases h : t%14=0
  · simp [h,GridEdge,ForwardEdge]; omega
  · simp [h,P.at_above h,GridEdge,ForwardEdge]; omega

theorem edge_hits_boundary {t a b} (adj : nextTo a b)
    (ha : P.pos a<t) (hb : t≤P.pos b) : P.At t (row (P.pos a)) a := by
  have e := (P.adjacent a b).mp adj
  unfold GridEdge ForwardEdge at e
  exact ⟨rfl,ha,by omega⟩

theorem occ_of_link {t r s} (h : P.Link t r s) : P.Occ t r := by
  obtain ⟨i,_,hi,_,_⟩ := h; exact ⟨i,hi⟩

theorem link_comm {t r s} : P.Link t r s ↔ P.Link t s r := by
  constructor <;> rintro ⟨i,j,hi,hj,h⟩ <;> exact ⟨j,i,hj,hi,joined_symm h⟩

end Ranked
end Height14
