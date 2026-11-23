import UniqueThree
import SubGameLib.Grundy

/-!
This optional comparison uses the author's original `Engine.lean` and
`Grundy.lean`. Run the following from this directory with the project toolchain.

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
LEAN_PATH="$dep:.lake/build/lib/lean" lean ManabeBridge.lean
```
-/

namespace SubtractionGame

/-- The three-entry mex agrees with Manabe's mex of the list of legal options. -/
private theorem step_eq_manabe (k n : Nat) (f : Nat → Nat) :
    step k f n = SubGame.mex4 (SubGame.opts f 3 8 (largeMove k) n) := by
  have hc : 0 < largeMove k := by unfold largeMove; omega
  by_cases h₃ : 3 ≤ n <;> by_cases h₈ : 8 ≤ n <;> by_cases h : largeMove k ≤ n <;>
    simp [step, SubGame.opts, hc, h₃, h₈, h, mex, SubGame.mex4] <;> grind

/-- Agreement at every heap size with the Grundy function in Manabe's
ancillary Lean sources for arXiv:2609.05358v2. -/
theorem eq_manabe (k n : Nat) :
    grundy k n = SubGame.grundy3 3 8 (largeMove k) n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have move (d : Nat) (hd : 0 < d) :
        (if d ≤ n then grundy k (n - d) else 4) =
        (if d ≤ n then SubGame.grundy3 3 8 (largeMove k) (n - d) else 4) := by
      split
      · exact ih (n - d) (by omega)
      · rfl
    rw [grundy_eq_step, SubGame.grundy3_eq 3 8 (largeMove k) n, ← step_eq_manabe]
    unfold step
    rw [move 3 (by decide), move 8 (by decide), move (largeMove k) (by unfold largeMove; omega)]

/-- The singleton theorem stated directly for Manabe's Grundy function. -/
theorem manabe_eq_three_iff (k n : Nat) (hk : 1 ≤ k) :
    SubGame.grundy3 3 8 (11 * k + 7) n = 3 ↔ n = 11 * k + 10 := by
  change SubGame.grundy3 3 8 (largeMove k) n = 3 ↔ _
  rw [← eq_manabe k n]
  exact grundy_eq_three_iff k n hk

end SubtractionGame
