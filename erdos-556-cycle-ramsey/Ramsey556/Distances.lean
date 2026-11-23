import Ramsey556.Basic

/-!
For vertices labelled from 0 to 32, monochromaticity of each of the four
edge-length classes 1, 2, 4 and 8 forces a monochromatic 9-cycle.
The six explicit cycle witnesses come from Result 3 of the
[Erdős Problem a Day working report](https://erdosproblemaday.com/report/556).
-/

namespace Ramsey556

/-- The absolute difference of two vertex labels. -/
def edgeLength {n : Nat} (u v : Fin n) : Nat :=
  max u.val v.val - min u.val v.val

/-- All edges of label difference `d` have color `k`. -/
def UniformAt {n : Nat} (c : Coloring n) (d : Nat) (k : Fin 3) : Prop :=
  ∀ u v, edgeLength u v = d → c.edge u v = k

private structure CycleRow where
  first : Nat
  second : Nat
  cycle : Vector (Fin 33) 9

private def rows : Vector CycleRow 6 := #v[
  ⟨1, 2, #v[0, 1, 3, 5, 7, 8, 6, 4, 2]⟩,
  ⟨1, 4, #v[0, 1, 2, 3, 7, 8, 9, 5, 4]⟩,
  ⟨1, 8, #v[0, 1, 2, 3, 4, 5, 6, 7, 8]⟩,
  ⟨2, 4, #v[0, 2, 6, 10, 14, 16, 12, 8, 4]⟩,
  ⟨2, 8, #v[0, 2, 4, 6, 14, 16, 18, 10, 8]⟩,
  ⟨4, 8, #v[0, 4, 12, 20, 28, 32, 24, 16, 8]⟩]

private theorem rows_simple :
    ∀ (r : Fin 6) (i j : Fin 9), rows[r].cycle[i] = rows[r].cycle[j] → i = j := by
  decide

private theorem rows_lengths : ∀ (r : Fin 6) (i : Fin 9),
    let d := edgeLength rows[r].cycle[i] rows[r].cycle[i+1]
    d = rows[r].first ∨ d = rows[r].second := by
  decide

private theorem useRow (c : Coloring 33) (r : Fin 6) {k l : Fin 3}
    (h₁ : UniformAt c rows[r].first k) (h₂ : UniformAt c rows[r].second l)
    (h : k = l) : HasMonoC9 c := by
  subst l
  refine ⟨k, fun i => rows[r].cycle[i], fun {i j} => rows_simple r i j, ?_⟩
  intro i
  rcases rows_lengths r i with hd | hd
  · exact h₁ _ _ hd
  · exact h₂ _ _ hd

/-- Colors on all other edge lengths can be arbitrary. -/
theorem hasMonoC9_of_four_distances (c : Coloring 33)
    (h₁ : ∃ k, UniformAt c 1 k) (h₂ : ∃ k, UniformAt c 2 k)
    (h₄ : ∃ k, UniformAt c 4 k) (h₈ : ∃ k, UniformAt c 8 k) : HasMonoC9 c := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  obtain ⟨d, hd⟩ := h₄
  obtain ⟨e, he⟩ := h₈
  have repeatColor : ∀ a b d e : Fin 3,
      a = b ∨ a = d ∨ a = e ∨ b = d ∨ b = e ∨ d = e := by decide
  rcases repeatColor a b d e with h | h | h | h | h | h
  · exact useRow c 0 ha hb h
  · exact useRow c 1 ha hd h
  · exact useRow c 2 ha he h
  · exact useRow c 3 hb hd h
  · exact useRow c 4 hb he h
  · exact useRow c 5 hd he h

/-- The upper bound at 33 for colorings that depend only on edge length. -/
theorem hasMonoC9_of_distance_coloring (c : Coloring 33) (f : Nat → Fin 3)
    (hf : ∀ u v, u ≠ v → c.edge u v = f (edgeLength u v)) : HasMonoC9 c := by
  have uniform (d : Nat) (hd : d ≠ 0) : ∃ k, UniformAt c d k := by
    refine ⟨f d, fun u v huv => ?_⟩
    have hne : u ≠ v := by
      rintro rfl
      simp [edgeLength] at huv
      exact hd huv.symm
    rw [hf u v hne, huv]
  exact hasMonoC9_of_four_distances c (uniform 1 (by decide)) (uniform 2 (by decide))
    (uniform 4 (by decide)) (uniform 8 (by decide))

end Ramsey556
