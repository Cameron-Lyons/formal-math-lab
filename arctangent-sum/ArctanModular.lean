module

public import ArctanBlock
public import ArctanReflection
import Mathlib.Tactic.Ring

@[expose] public section

namespace Arxiv.«2607.05739»

-- The two coordinates of the Gaussian product in the residue field.
private abbrev reMod (p n : ℕ) : ZMod p := ((coords n).1 : ZMod p)
private abbrev imMod (p n : ℕ) : ZMod p := ((coords n).2 : ZMod p)

private theorem mod_succ (p n : ℕ) :
    reMod p (n + 1) = reMod p n - (n + 1 : ZMod p) * imMod p n ∧
    imMod p (n + 1) = imMod p n + (n + 1 : ZMod p) * reMod p n := by
  simp [reMod, imMod, coords]

/-- Shifting by a full block multiplies the two coordinates by the same scalar
if the imaginary coordinate of the full block vanishes. -/
private theorem shift_block (p : ℕ) (h : imMod p p = 0) (n : ℕ) :
    reMod p (p + n) = reMod p p * reMod p n ∧
    imMod p (p + n) = reMod p p * imMod p n := by
  induction n with
  | zero => simp [reMod, imMod, coords] at *; exact h
  | succ n ih =>
    rw [← Nat.add_assoc, (mod_succ p (p + n)).1, (mod_succ p (p + n)).2,
      ih.1, ih.2, (mod_succ p n).1, (mod_succ p n).2]
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    constructor <;> ring

/-- Removing complete blocks preserves both coordinates up to the same nonzero factor. -/
private theorem remove_blocks (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3) (q r : ℕ) :
    ∃ c : ZMod p, c ≠ 0 ∧ reMod p (p * q + r) = c * reMod p r ∧
      imMod p (p * q + r) = c * imMod p r := by
  obtain ⟨hr, hi⟩ := inert_block p hp
  induction q with
  | zero => exact ⟨1, one_ne_zero, by simp, by simp⟩
  | succ q ih =>
    obtain ⟨c, hc, h₁, h₂⟩ := ih
    rw [show p * (q + 1) + r = p + (p * q + r) by ring]
    obtain ⟨hs₁, hs₂⟩ := shift_block p hi (p * q + r)
    exact ⟨_, mul_ne_zero hr hc, by rw [hs₁, h₁, mul_assoc],
      by rw [hs₂, h₂, mul_assoc]⟩

/-- A zero real coordinate modulo an inert prime excludes the entire progression. -/
theorem not_isIntegerValue_of_inert_prime {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {r : ℕ} (hr : ((coords r).1 : ZMod p) = 0) (q : ℕ) :
    ¬ IsIntegerValue (p * q + r) := by
  obtain ⟨c, hc, h₁, h₂⟩ := remove_blocks p hp q r
  obtain hi := coords_snd_ne_zero_of_fst_eq_zero p hp r hr
  have hzero : reMod p (p * q + r) = 0 := h₁.trans (mul_eq_zero_of_right c hr)
  have hne : imMod p (p * q + r) ≠ 0 := h₂.trans_ne (mul_ne_zero hc hi)
  rintro hv
  obtain ⟨m, hm⟩ := (isIntegerValue_iff_coords _).mp hv
  apply hne
  change ((coords _).2 : ZMod p) = 0
  rw [hm, Int.cast_mul]
  exact mul_eq_zero_of_left hzero _

/-- An integer value at any index is represented modulo every inert prime by
a prefix of at most half a block. -/
theorem integer_value_mem_residues {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {n : ℕ} {m : ℤ} (h : B n = A n * m) :
    ∃ r : Fin (p / 2 + 1), ((coords r.val).1 : ZMod p) ≠ 0 ∧
      ((coords r.val).2 : ZMod p) = (coords r.val).1 * (m : ZMod p) := by
  let r := n % p
  have hr : r < p := Nat.mod_lt _ (Fact.out : p.Prime).pos
  obtain ⟨c, hc, h₁, h₂⟩ := remove_blocks p hp (n / p) r
  have hn : p * (n / p) + r = n := (Nat.div_add_mod n p)
  rw [hn] at h₁ h₂
  have hcast : imMod p n = reMod p n * (m : ZMod p) := by
    simpa [imMod, reMod, coords_eq] using congrArg (Int.cast : ℤ → ZMod p) h
  rw [h₁, h₂, mul_assoc] at hcast
  have hratio := mul_left_cancel₀ hc hcast
  have hne {j : ℕ} (hj : imMod p j = reMod p j * (m : ZMod p)) : reMod p j ≠ 0 := by
    intro hz
    exact coords_snd_ne_zero_of_fst_eq_zero p hp j hz (hj.trans (mul_eq_zero_of_left hz _))
  by_cases hsmall : r ≤ p / 2
  · exact ⟨⟨r, by omega⟩, hne hratio, hratio⟩
  · have href := coords_reflection p r (by exact ⟨p / 2, by omega⟩) hr
    change reMod p r * imMod p (p - 1 - r) = imMod p r * reMod p (p - 1 - r) at href
    rw [hratio, mul_assoc, mul_comm (m : ZMod p)] at href
    have hratio' := mul_left_cancel₀ (hne hratio) href
    exact ⟨⟨p - 1 - r, by omega⟩, hne hratio', hratio'⟩

end Arxiv.«2607.05739»
