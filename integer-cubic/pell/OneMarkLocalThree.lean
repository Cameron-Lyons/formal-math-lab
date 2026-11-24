module

public import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Zify

public section

namespace SmallCubic.OneMarkLocalThree

private theorem residue_check : ∀ a b c : Fin 9,
    (3 * (a.val ^ 3 + b.val ^ 2 * c.val) + c.val ^ 2) % 9 = 0 →
    a.val % 3 = 0 ∧ c.val % 3 = 0 := by decide +kernel

/-- If all three leading coefficients vanish modulo 3, their degree-24
equation modulo 81 forces the leading coefficients of X and Z to vanish modulo 9. -/
theorem leading_coefficients (x y z : ℤ) (hx : 3 ∣ x) (hy : 3 ∣ y) (hz : 3 ∣ z)
    (h : 81 ∣ x^3 + y^2*z + z^2) : 9 ∣ x ∧ 9 ∣ z := by
  obtain ⟨a,rfl⟩ := hx
  obtain ⟨b,rfl⟩ := hy
  obtain ⟨c,rfl⟩ := hz
  obtain ⟨k,hk⟩ := h
  have hd : 3 * (a^3 + b^2*c) + c^2 = 9*k := by
    have hg : 9 * (3 * (a^3 + b^2*c) + c^2) = 9 * (9*k) := by linear_combination hk
    omega
  have cong (w : ℤ) : w ≡ w % 9 [ZMOD 9] := (Int.mod_modEq w 9).symm
  have hc := ((Int.ModEq.refl (3 : ℤ)).mul
    (((cong a).pow 3).add (((cong b).pow 2).mul (cong c)))).add ((cong c).pow 2)
  rw [hd] at hc
  change 9*k % 9 = _ at hc
  have da : 0 ≤ a % 9 := Int.emod_nonneg _ (by decide)
  have db : 0 ≤ b % 9 := Int.emod_nonneg _ (by decide)
  have dc : 0 ≤ c % 9 := Int.emod_nonneg _ (by decide)
  let af : Fin 9 := ⟨(a % 9).toNat, by omega⟩
  let bf : Fin 9 := ⟨(b % 9).toNat, by omega⟩
  let cf : Fin 9 := ⟨(c % 9).toNat, by omega⟩
  have hh : (3*(af.val^3+bf.val^2*cf.val)+cf.val^2)%9=0 := by
    zify
    simpa [af, bf, cf, Int.toNat_of_nonneg da, Int.toNat_of_nonneg db,
      Int.toNat_of_nonneg dc] using hc.symm
  obtain ⟨ha,hc'⟩ := residue_check af bf cf hh
  dsimp [af,cf] at ha hc'
  omega

end SmallCubic.OneMarkLocalThree
