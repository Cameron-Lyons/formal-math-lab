import Extended

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace TBoards

/-- The larger explicit family, whose entries all carry validity proofs. -/
def extendedFamily : List Board := certifiedValues (Extended.blocks.flatMap CodeBlock.boards)

theorem extendedFamily_length : extendedFamily.length = 17160 := by
  have h := congrArg List.length (codeBlocks_correct Extended.blocks)
  simp only [List.length_map] at h
  exact h.trans (by decide +kernel)

theorem extendedFamily_nodup : extendedFamily.Nodup := by
  apply nodup_of_increasing_codes
  change increasing ((certifiedValues (Extended.blocks.flatMap CodeBlock.boards)).map boardCode) = true
  rw [codeBlocks_correct]
  decide +kernel

theorem extendedFamily_valid : ∀ b ∈ extendedFamily, Valid b :=
  certifiedValues_valid _

/-- At least 17160 distinct labeled three-color T boards exist. -/
theorem at_least_17160 :
    ∃ f : Fin 17160 → Board, (∀ i, Valid (f i)) ∧
      (∀ i j, f i = f j → i = j) := by
  exact injective_family_of_list extendedFamily 17160
    (by rw [extendedFamily_length]; exact Nat.le_refl 17160)
    extendedFamily_nodup extendedFamily_valid

end TBoards

#print axioms TBoards.at_least_17160
