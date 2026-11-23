import Std

namespace Ramsey556

theorem select_vertices {α : Type} (xs : List α) (distinct : xs.Nodup) (m : Nat) (large : m ≤ xs.length) :
    ∃ v : Fin m → α, Function.Injective v ∧ ∀ i, v i ∈ xs := by
  let v (i : Fin m) := xs[i.val]'(Nat.lt_of_lt_of_le i.isLt large)
  exact ⟨v, fun {_ _} eq => Fin.ext (distinct.eq_of_getElem_eq _ _ eq), fun _ => List.getElem_mem ..⟩

/-- Enumerate any requested number of distinct vertices satisfying a test. -/
theorem select_where {n m : Nat} (p : Fin n → Bool)
    (enough : m ≤ ((List.finRange n).filter p).length) :
    ∃ v : Fin m → Fin n, Function.Injective v ∧ ∀ i, p (v i) = true := by
  obtain ⟨v, inj, mem⟩ := select_vertices _ ((List.nodup_finRange n).filter p) m enough
  exact ⟨v, inj, fun i => (List.mem_filter.mp (mem i)).2⟩

theorem large_side {α : Type} (xs : List α) (side : α → Bool)
    (m : Nat) (h : 2 * m < xs.length) :
    ∃ b : Bool, m < (xs.filter (fun x => side x == b)).length := by
  have total : xs.length = (xs.filter (fun x => side x == true)).length +
      (xs.filter (fun x => side x == false)).length := by
    simpa [List.countP_eq_length_filter] using List.length_eq_countP_add_countP side (l := xs)
  by_cases ht : m < (xs.filter (fun x => side x == true)).length
  · exact ⟨true, ht⟩
  · exact ⟨false, by omega⟩

/-- Among more than twice m vertices, at least m+1 have the same Boolean label. -/
theorem select_side {n m : Nat} (side : Fin n → Bool) (room : 2 * m < n) :
    ∃ (v : Fin (m+1) → Fin n) (b : Bool), Function.Injective v ∧ ∀ i, side (v i) = b := by
  obtain ⟨b,large⟩ := large_side (List.finRange n) side m (by simpa using room)
  obtain ⟨v,inj,same⟩ := select_where (fun x => side x == b) large
  exact ⟨v,b,inj,fun i => beq_iff_eq.mp (same i)⟩

/-- Choose vertices outside the image of a labeling. Its image has size at most a. -/
theorem outside_vertices {n a b : Nat} (room : a + b ≤ n) (v : Fin a → Fin n) :
    ∃ w : Fin b → Fin n, Function.Injective w ∧ ∀ i j, v i ≠ w j := by
  let image := (List.finRange a).map v
  let used (x : Fin n) := image.contains x
  have bound : ((List.finRange n).filter used).length ≤ a := by
    have sub : (List.finRange n).filter used ⊆ image := fun {_} h =>
      List.contains_iff_mem.mp (List.mem_filter.mp h).2
    simpa [image] using List.Nodup.length_le_of_subset ((List.nodup_finRange n).filter used) sub
  have counts := List.length_eq_countP_add_countP used (l := List.finRange n)
  simp [List.countP_eq_length_filter] at counts
  obtain ⟨w, inj, outside⟩ := select_where (m := b) (fun x => !used x) (by omega)
  refine ⟨w, inj, ?_⟩
  intro i j eq
  have mem : w j ∈ image := List.mem_map.mpr ⟨i,List.mem_finRange _,eq⟩
  exact (show w j ∉ image by simpa [used] using outside j) mem

end Ramsey556
