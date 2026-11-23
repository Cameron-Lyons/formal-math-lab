import SevenCycle.Lower
import SevenCycle.CheckedSeeds

namespace SevenCycle

/-- Among ten edges at one vertex, four have the same color. The finite
star lemma then supplies a seven-cycle with at most two color changes. -/
theorem eleven_forces : ForcesSeven 11 := forces_eleven_of_star star_forces_seven

/-- The exact threshold for a seven-cycle with at most two color changes is 11. -/
theorem exact_threshold (n : Nat) : ForcesSeven n ↔ 11 ≤ n := by
  constructor
  · intro h
    apply Nat.lt_of_not_ge
    intro hn
    exact ten_does_not_force (forces_mono hn h)
  · intro hn
    exact forces_mono hn eleven_forces

end SevenCycle
