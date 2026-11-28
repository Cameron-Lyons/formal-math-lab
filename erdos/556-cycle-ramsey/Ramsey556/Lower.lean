import Ramsey556.Bipartite

namespace Ramsey556

/-- Split 32 vertices into two halves and each half into two blocks of eight.
Color 0 joins halves, color 1 joins blocks within a half, and color 2 stays in a block. -/
def lowerColoring : Coloring 32 where
  edge u v :=
    if u.val / 16 = v.val / 16 then
      if u.val / 8 = v.val / 8 then 2 else 1
    else 0
  symm u v := by simp only [eq_comm]

theorem sum_ne_one_around_cycle (f : Fin 9 → Nat)
    (edges : ∀ i, f i + f (i + 1) = 1) : False := by
  have h0 : f 0 + f 1 = 1 := edges 0
  have h1 : f 1 + f 2 = 1 := edges 1
  have h2 : f 2 + f 3 = 1 := edges 2
  have h3 : f 3 + f 4 = 1 := edges 3
  have h4 : f 4 + f 5 = 1 := edges 4
  have h5 : f 5 + f 6 = 1 := edges 5
  have h6 : f 6 + f 7 = 1 := edges 6
  have h7 : f 7 + f 8 = 1 := edges 7
  have h8 : f 8 + f 0 = 1 := edges 8
  omega

theorem constant_along_cycle {α : Type} (f : Fin 9 → α)
    (edges : ∀ i, f i = f (i + 1)) (i : Fin 9) : f i = f 0 := by
  obtain ⟨j, hj⟩ := i
  induction j with
  | zero => rfl
  | succ j ih =>
    let k : Fin 9 := ⟨j, by omega⟩
    have hs : k + 1 = (⟨j + 1, hj⟩ : Fin 9) := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt hj
    rw [← hs, ← edges k]
    exact ih (by omega)

theorem no_injection_nine_eight (f : Fin 9 → Fin 8)
    (hinj : ∀ ⦃i j⦄, f i = f j → i = j) : False := by
  have nd : ((List.finRange 9).map f).Nodup :=
    (List.nodup_finRange 9).map f (fun _ _ h eq => h (hinj eq))
  have le := nd.length_le_of_subset (l₂ := List.finRange 8) (fun {_} _ => List.mem_finRange _)
  simp at le

theorem lowerColoring_no_monoC9 : ¬ HasMonoC9 lowerColoring := by
  rintro ⟨k, v, hinj, edges⟩
  have cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases cases with rfl | rfl | rfl
  · -- A color-0 edge switches halves.
    have switches : ∀ x y : Fin 32, lowerColoring.edge x y = 0 →
        x.val / 16 + y.val / 16 = 1 := by decide
    exact sum_ne_one_around_cycle (fun i => (v i).val / 16)
      (fun i => switches _ _ (edges i))
  · -- A color-1 edge switches the block bit within its half.
    have switches : ∀ x y : Fin 32, lowerColoring.edge x y = 1 →
        (x.val / 8) % 2 + (y.val / 8) % 2 = 1 := by decide
    exact sum_ne_one_around_cycle (fun i => ((v i).val / 8) % 2)
      (fun i => switches _ _ (edges i))
  · -- All nine vertices of a color-2 cycle would lie in one block.
    have same : ∀ x y : Fin 32, lowerColoring.edge x y = 2 →
        x.val / 8 = y.val / 8 := by decide
    have block := constant_along_cycle (fun i => (v i).val / 8)
      (fun i => same _ _ (edges i))
    let offset (i : Fin 9) : Fin 8 := ⟨(v i).val % 8, Nat.mod_lt _ (by decide)⟩
    apply no_injection_nine_eight offset
    intro i j heq
    apply hinj
    apply Fin.ext
    have hij := congrArg Fin.val heq
    change (v i).val % 8 = (v j).val % 8 at hij
    have hi : (v i).val / 8 = (v 0).val / 8 := block i
    have hj : (v j).val / 8 = (v 0).val / 8 := block j
    omega

/-- This obstruction already has two bipartite colors before deleting any vertex. -/
theorem lowerColoring_two_bipartite :
    IsBipartiteColor lowerColoring 0 ∧ IsBipartiteColor lowerColoring 1 := by
  constructor
  · exact ⟨fun u => decide (u.val < 16), by decide⟩
  · exact ⟨fun u => decide ((u.val / 8) % 2 = 0), by decide⟩

end Ramsey556
