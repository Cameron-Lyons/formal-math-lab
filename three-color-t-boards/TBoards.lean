import Std

/-!
# Three-color T boards

A board is stored from top to bottom and left to right. Row `r` starts at
horizontal coordinate `-r` and contains `2*r+1` cells. Colors are `0,1,2`.
A placement `(r,j)` consists of upper cell `(r,j)` and the three lower cells
`(r+1,j)`, `(r+1,j+1)`, `(r+1,j+2)`. Thus the upper cell is directly above
the middle lower cell: both have horizontal coordinate `j-r`.
-/
namespace TBoards

abbrev Board := List (List Nat)
abbrev Placement := Nat × Nat
/-- Ordered colors: upper, lower-left, lower-middle, lower-right. -/
abbrev Pattern := Nat × Nat × Nat × Nat

def cell (b : Board) (r j : Nat) : Nat := (b.getD r []).getD j 0

def placements : List Placement :=
  (List.range 9).flatMap fun r => (List.range (2*r+1)).map fun j => (r,j)

def IsPlacement (p : Placement) : Prop := p.1 < 9 ∧ p.2 < 2*p.1+1

def patternAt (b : Board) (p : Placement) : Pattern :=
  (cell b p.1 p.2, cell b (p.1+1) p.2,
   cell b (p.1+1) (p.2+1), cell b (p.1+1) (p.2+2))

def patterns (b : Board) : List Pattern := placements.map (patternAt b)

def WellFormed (b : Board) : Prop :=
  b.length = 10 ∧
  (∀ r ∈ List.range 10, (b.getD r []).length = 2*r+1) ∧
  (∀ row ∈ b, ∀ c ∈ row, c < 3)

/-- Every one of the 81 ordered color patterns occurs exactly once. -/
def Valid (b : Board) : Prop :=
  WellFormed b ∧
  ∀ a l m r : Fin 3, (patterns b).count (a.val,l.val,m.val,r.val) = 1

instance (b : Board) : Decidable (WellFormed b) := by
  unfold WellFormed
  infer_instance

instance (b : Board) : Decidable (Valid b) := by
  unfold Valid
  infer_instance

/-- A finite, explicit meaning of the asserted strict lower bound. -/
def MoreThanSixty : Prop :=
  ∃ bs : List Board, 60 < bs.length ∧ bs.Nodup ∧ ∀ b ∈ bs, Valid b

theorem placements_length : placements.length = 81 := by decide

theorem placements_nodup : placements.Nodup := by decide

theorem mem_placements (p : Placement) : p ∈ placements ↔ IsPlacement p := by
  rcases p with ⟨r,j⟩
  simp [placements, IsPlacement]

theorem patterns_length (b : Board) : (patterns b).length = 81 := by
  simp [patterns, placements_length]

theorem Valid.pattern_count {b : Board} (h : Valid b)
    (a l m r : Nat) (ha : a < 3) (hl : l < 3) (hm : m < 3) (hr : r < 3) :
    (patterns b).count (a,l,m,r) = 1 :=
  h.2 ⟨a,ha⟩ ⟨l,hl⟩ ⟨m,hm⟩ ⟨r,hr⟩

/-- Every requested cell is an actual board entry and has one of the three colors.
The default values in `cell` are therefore irrelevant on board coordinates. -/
theorem WellFormed.cell_is_entry {b : Board} (h : WellFormed b)
    (r j : Nat) (hr : r < 10) (hj : j < 2*r+1) :
    ∃ row, row ∈ b ∧ row.length = 2*r+1 ∧ cell b r j ∈ row ∧ cell b r j < 3 := by
  have hrb : r < b.length := by have := h.1; omega
  have hrow : b.getD r [] ∈ b := by
    rw [← List.getElem_eq_getD [] (h := hrb)]
    exact List.getElem_mem hrb
  have hlen : (b.getD r []).length = 2*r+1 := h.2.1 r (List.mem_range.mpr hr)
  have hjrow : j < (b.getD r []).length := by omega
  have hcell : cell b r j ∈ b.getD r [] := by
    unfold cell
    rw [← List.getElem_eq_getD 0 (h := hjrow)]
    exact List.getElem_mem hjrow
  exact ⟨b.getD r [], hrow, hlen, hcell, h.2.2 _ hrow _ hcell⟩

/-- All four offsets of every enumerated T lie within their respective rows. -/
theorem placement_bounds {p : Placement} (h : IsPlacement p) :
    p.1 < 10 ∧ p.2 < 2*p.1+1 ∧
    p.1+1 < 10 ∧ p.2 < 2*(p.1+1)+1 ∧
    p.2+1 < 2*(p.1+1)+1 ∧ p.2+2 < 2*(p.1+1)+1 := by
  unfold IsPlacement at h
  omega

/-- Count-one in the finite placement list entails existence and uniqueness
of an actual geometric placement, without assuming a search program correct. -/
theorem Valid.unique_placement {b : Board} (h : Valid b)
    (a l m r : Fin 3) :
    ∃ p, IsPlacement p ∧ patternAt b p = (a.val,l.val,m.val,r.val) ∧
      ∀ q, IsPlacement q → patternAt b q = (a.val,l.val,m.val,r.val) → q = p := by
  let target : Pattern := (a.val,l.val,m.val,r.val)
  have hc : (patterns b).count target = 1 := h.2 a l m r
  have hf : (placements.filter fun p => patternAt b p == target).length = 1 := by
    rw [patterns, List.count_eq_countP, List.countP_map,
      List.countP_eq_length_filter] at hc
    exact hc
  obtain ⟨p, hp⟩ := List.length_eq_one_iff.mp hf
  have hp_mem : p ∈ placements.filter (fun q => patternAt b q == target) := by
    rw [hp]
    simp
  obtain ⟨hp_place, hp_target⟩ := List.mem_filter.mp hp_mem
  refine ⟨p, (mem_placements p).mp hp_place, by simpa using hp_target, ?_⟩
  intro q hq hq_target
  have hq_mem : q ∈ placements.filter (fun q => patternAt b q == target) :=
    List.mem_filter.mpr ⟨(mem_placements q).mpr hq, by simpa using hq_target⟩
  simpa [hp] using hq_mem

/-- A duplicate-free certificate list yields an indexed family of any
requested size up to its length. -/
theorem injective_family_of_list (bs : List Board) (n : Nat)
    (hlen : n ≤ bs.length) (hn : bs.Nodup) (hv : ∀ b ∈ bs, Valid b) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  let f : Fin n → Board := fun i => bs[i.val]'(by have := i.isLt; omega)
  refine ⟨f, ?_, ?_⟩
  · intro i
    exact hv (f i) (List.getElem_mem (by have := i.isLt; omega))
  · intro i j hij
    apply Fin.ext
    exact hn.eq_of_getElem_eq (by have := i.isLt; omega)
      (by have := j.isLt; omega) hij

/-- The list lower-bound statement supplies 61 pairwise different valid boards. -/
theorem MoreThanSixty.injective_family (h : MoreThanSixty) :
    ∃ f : Fin 61 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  obtain ⟨bs, hlen, hn, hv⟩ := h
  exact injective_family_of_list bs 61 (by omega) hn hv

end TBoards
