import BoardData

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards

/- Each `decide` proof below is reduced and checked by the Lean kernel.
   No external solver, native_decide, or additional axiom is used. -/

theorem novel_valid : Valid novel := by decide +kernel

theorem novel_not_published : novel ∉ published := by decide +kernel

theorem published_length : published.length = 60 := by decide +kernel

theorem new_orbit_length : newOrbit.length = 12 := by decide +kernel

theorem family_length : family.length = 72 := by decide +kernel

theorem family_nodup : family.Nodup := by decide +kernel

theorem orbit0_valid : ∀ b ∈ orbit seed0, Valid b := by decide +kernel
theorem orbit1_valid : ∀ b ∈ orbit seed1, Valid b := by decide +kernel
theorem orbit2_valid : ∀ b ∈ orbit seed2, Valid b := by decide +kernel
theorem orbit3_valid : ∀ b ∈ orbit seed3, Valid b := by decide +kernel
theorem orbit4_valid : ∀ b ∈ orbit seed4, Valid b := by decide +kernel
theorem orbit5_valid : ∀ b ∈ orbit seed5, Valid b := by decide +kernel

theorem family_valid : ∀ b ∈ family, Valid b := by
  intro b hb
  rcases List.mem_append.mp hb with hp | hn
  · change b ∈ publishedSeeds.flatMap orbit at hp
    obtain ⟨s, hs, hb⟩ := List.mem_flatMap.mp hp
    simp [publishedSeeds] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl
    · exact orbit0_valid b hb
    · exact orbit1_valid b hb
    · exact orbit2_valid b hb
    · exact orbit3_valid b hb
    · exact orbit4_valid b hb
  · exact orbit5_valid b hn

/-- There are at least 72 distinct labeled boards meeting the question's rule. -/
theorem at_least_72 :
    ∃ f : Fin 72 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  exact injective_family_of_list family 72 (by rw [family_length]; exact Nat.le_refl 72)
    family_nodup family_valid

/-- In particular, the answer to “are there more than 60?” is yes. -/
theorem more_than_60 : MoreThanSixty := by
  exact ⟨family, by rw [family_length]; decide, family_nodup, family_valid⟩

/-- An explicit witness outside the complete published 60-board list. -/
theorem new_board_exists : ∃ b : Board, Valid b ∧ b ∉ published :=
  ⟨novel, novel_valid, novel_not_published⟩

end TBoards

#print axioms TBoards.at_least_72
#print axioms TBoards.more_than_60
#print axioms TBoards.new_board_exists
