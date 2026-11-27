import ResidueOne
import SubGameLib.Grundy

/-!
This optional comparison uses Manabe's original ancillary Lean sources for
arXiv:2609.05358v2. To check it, run from the directory containing this file.

```sh
dep=$(mktemp -d)
mkdir -p "$dep/SubGameLib"
src=https://arxiv.org/src/2609.05358v2/anc/lean-verification/SubGameLib
for mod in Engine Grundy; do
  curl -fsSL "$src/$mod.lean" -o "$dep/SubGameLib/$mod.lean" || exit 1
  LEAN_PATH="$dep" lean --root="$dep" -o "$dep/SubGameLib/$mod.olean" \
    "$dep/SubGameLib/$mod.lean" || exit 1
done
lake build
LEAN_PATH="$dep" lake env lean ManabeBridge.lean
```
-/

namespace SubtractionGame.ThirdMove

private theorem step_eq_manabe (c n : Nat) (f : Nat → Nat) :
    step c f n = SubGame.mex4 (SubGame.opts f 3 8 c n) := by
  by_cases h₃ : 3 ≤ n <;> by_cases h₈ : 8 ≤ n <;> by_cases hc : 0 < c ∧ c ≤ n <;>
    simp [step, SubGame.opts, h₃, h₈, hc, mex, SubGame.mex4] <;> grind

/-- Both Grundy definitions agree for every heap and every third move. -/
theorem eq_manabe (c n : Nat) : grundy c n = SubGame.grundy3 3 8 c n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [grundy_eq_step, SubGame.grundy3_eq 3 8 c n, ← step_eq_manabe]
    unfold step
    congr 1 <;> split <;> first | rfl | apply ih <;> omega

end SubtractionGame.ThirdMove

namespace SubtractionGame.ResidueOne

/-- The singleton value 3 for the Grundy function in Manabe's ancillary sources. -/
theorem manabe_eq_three_iff (k n : Nat) (hk : 1 ≤ k) :
    SubGame.grundy3 3 8 (11 * k + 1) n = 3 ↔ n = 11 * k + 4 := by
  rw [← ThirdMove.eq_manabe]
  exact grundy_eq_three_iff k n hk

end SubtractionGame.ResidueOne
