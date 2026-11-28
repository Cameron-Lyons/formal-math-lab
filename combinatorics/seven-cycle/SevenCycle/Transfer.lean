import SevenCycle.Basic

namespace SevenCycle

/-- Restrict to the selected vertices and rename the colors. -/
def Coloring.pullback (c : Coloring n) (ι : Fin m → Fin n) (σ : Color → Color) :
    Coloring m where
  edge x y := σ (c.edge (ι x) (ι y))
  symm x y := congrArg σ (c.symm (ι x) (ι y))

private theorem rotate_map (xs : List α) (f : α → β) :
    (xs.map f).rotateLeft 1 = (xs.rotateLeft 1).map f := by
  simp only [List.rotateLeft, List.length_map]
  split <;> simp

theorem hasGoodSeven_of_pullback (c : Coloring n) (ι : Fin m → Fin n) (σ : Color → Color)
    (hi : ∀ ⦃x y⦄, ι x = ι y → x = y) (hs : ∀ ⦃x y⦄, σ x = σ y → x = y) :
    HasGoodSeven (c.pullback ι σ) → HasGoodSeven c := by
  rintro ⟨xs, hlen, hnodup, hchanges⟩
  refine ⟨xs.map ι, by simpa, List.pairwise_map.mpr (hnodup.imp fun h he => h (hi he)), ?_⟩
  have hj (a b : Color) : jump (σ a) (σ b) = jump a b := by
    simp [jump, show σ a = σ b ↔ a = b from ⟨fun h => hs h, congrArg σ⟩]
  let es := xs.zipWith (fun a b => c.edge (ι a) (ι b)) (xs.rotateLeft 1)
  have hcolors : xs.zipWith (c.pullback ι σ).edge (xs.rotateLeft 1) = es.map σ :=
    List.map_zipWith.symm
  simp only [changes, hcolors, rotate_map, List.zipWith_map, hj] at hchanges ⊢
  exact hchanges

theorem forces_mono {m n : Nat} (hmn : m ≤ n) (hm : ForcesSeven m) : ForcesSeven n := by
  intro c
  let ι := fun x : Fin m => x.castLE hmn
  exact hasGoodSeven_of_pullback c ι id (fun {_ _} h => Fin.ext (congrArg (fun z : Fin n => z.val) h))
    (fun {_ _} h => h) (hm _)

private theorem three_classes (color : α → Color) (xs : List α) :
    (xs.filter (fun x => color x == 0)).length +
    (xs.filter (fun x => color x == 1)).length +
    (xs.filter (fun x => color x == 2)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h : color x = 0 ∨ color x = 1 ∨ color x = 2 := by
      exact (by decide : ∀ y : Color, y = 0 ∨ y = 1 ∨ y = 2) _
    rcases h with h | h | h <;>
      simp only [List.filter_cons, h, List.length_cons] <;> simp <;> omega

private def rename (t x : Color) : Color :=
  if x = t then 0 else if x = 0 then t else x

private theorem rename_zero (t : Color) : rename t t = 0 := by simp [rename]

private theorem rename_inj (t : Color) : ∀ ⦃x y⦄, rename t x = rename t y → x = y := by
  decide +revert

/-- At any vertex of K₁₁, four of its ten incident edges have the same color.
Place four such neighbors first, keep nine neighbors in total, and rename that
common color to zero. -/
theorem forces_eleven_of_star
    (solve : ∀ c : Coloring 10, c.edge 0 1 = 0 → c.edge 0 2 = 0 →
      c.edge 0 3 = 0 → c.edge 0 4 = 0 → HasGoodSeven c) : ForcesSeven 11 := by
  intro c
  let leaves : List (Fin 11) := List.ofFn (fun x : Fin 10 => x.succ)
  have lsize : leaves.length = 10 := by simp [leaves]
  have ht : ∃ t : Color, 4 ≤ (leaves.filter (fun x => c.edge 0 x == t)).length := by
    have counts := three_classes (c.edge 0) leaves
    by_cases h₀ : 4 ≤ (leaves.filter (fun x => c.edge 0 x == 0)).length
    · exact ⟨0, h₀⟩
    by_cases h₁ : 4 ≤ (leaves.filter (fun x => c.edge 0 x == 1)).length
    · exact ⟨1, h₁⟩
    exact ⟨2, by omega⟩
  obtain ⟨t, ht⟩ := ht
  let preferred := fun x => c.edge 0 x == t
  let first := leaves.filter preferred
  let rest := leaves.filter (fun x => !preferred x)
  let order := (0 : Fin 11) :: (first ++ rest)
  have perm : order.Perm (0 :: leaves) :=
    List.Perm.cons _ (List.filter_append_perm preferred leaves)
  have orderSize : order.length = 11 := perm.length_eq
  have distinct : order.Nodup := perm.nodup_iff.mpr (by decide)
  let ι (x : Fin 10) : Fin 11 := order[x.val]'(by omega)
  have hi : ∀ ⦃x y⦄, ι x = ι y → x = y :=
    fun {_ _} h => Fin.ext (distinct.eq_of_getElem_eq _ _ h)
  have colored (k : Nat) (hk : k < 4) :
      c.edge 0 (ι ⟨k+1, by omega⟩) = t := by
    change 4 ≤ first.length at ht
    have hfirst : k < first.length := by omega
    change c.edge 0 ((first ++ rest)[k]'(by simp; omega)) = t
    rw [List.getElem_append_left hfirst]
    exact beq_iff_eq.mp (List.mem_filter.mp (List.getElem_mem hfirst)).2
  apply hasGoodSeven_of_pullback c ι (rename t) hi (rename_inj t)
  apply solve <;> change rename t (c.edge 0 (ι _)) = 0
  · exact (congrArg (rename t) (colored 0 (by decide))).trans (rename_zero t)
  · exact (congrArg (rename t) (colored 1 (by decide))).trans (rename_zero t)
  · exact (congrArg (rename t) (colored 2 (by decide))).trans (rename_zero t)
  · exact (congrArg (rename t) (colored 3 (by decide))).trans (rename_zero t)

end SevenCycle
