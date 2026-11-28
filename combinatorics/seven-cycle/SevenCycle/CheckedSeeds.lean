import SevenCycle.Search
import SevenCycle.Seed

namespace SevenCycle

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
/-- All canonical colorings of the four star leaves force a good seven-cycle.
For each pattern the search tries all three colors on each new edge until
it finds a good seven-cycle. -/
theorem Cert.checked_seed : ∀ s ∈ canonicalSeeds, Cert.Valid (Cert.seedMask s) := by
  simp only [canonicalSeeds, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals first | exact List.forall_mem_nil _ | as_aux_lemma => search_star

/-- A monochromatic star on four leaves already forces the cycle in K₁₀.
The center and the leaves are labeled 0 and 1 through 4, respectively. -/
theorem star_forces_seven (c : Coloring 10) (h₁ : c.edge 0 1 = 0) (h₂ : c.edge 0 2 = 0)
    (h₃ : c.edge 0 3 = 0) (h₄ : c.edge 0 4 = 0) : HasGoodSeven c := by
  apply normalizeSeed _ c h₁ h₂ h₃ h₄
  intro d h₁ h₂ h₃ h₄ hs
  apply Cert.checked_seed (seedCode d) hs d
  apply Cert.covers_seed d _ h₁ h₂ h₃ h₄
  all_goals
    unfold seedCode packSeed
    omega

end SevenCycle
