module

public import Slots
public import Mathlib.Data.List.MinMax

@[expose] public section

namespace Erdos708Slots

/-- Pick the site supplying the largest divisor of the remaining target. -/
private def greedy (period : ℕ) : ℕ → ℕ → List ℕ → Finset ℕ
  | 0, _, _ => ∅
  | k+1, t, sites =>
    let gain := fun b => (period.gcd b).gcd t
    match sites.argmax gain with
    | none => ∅
    | some b => insert b (greedy period k (t / gain b) (sites.erase b))

private theorem lift_residue {M D t : ℕ} (L : ℕ) (hD : 0 < D)
    (cert : ∀ r : Fin D, let S := greedy D 8 t ((List.range M).map (r.val + ·))
      S ⊆ Finset.Ico r.val (r.val+M) ∧ S.card ≤ 8 ∧ t ∣ ∏ x ∈ S, Nat.gcd D x) :
    Cover L M 8 t := by
  let r : Fin D := ⟨L % D, Nat.mod_lt _ hD⟩
  let S := greedy D 8 t ((List.range M).map (r.val + ·))
  obtain ⟨hS,hcard,hprod⟩ := cert r
  let shift := L - L%D
  have hshift : shift + r.val = L := Nat.sub_add_cancel (Nat.mod_le ..)
  have hdvd : D ∣ shift := Nat.dvd_sub_mod L
  refine ⟨S.image (shift + ·), ?_, Finset.card_image_le.trans hcard, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1,h2⟩ := Finset.mem_Ico.mp (hS hs)
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · rw [Finset.prod_image (fun _ _ _ _ heq => Nat.add_left_cancel heq)]
    apply hprod.trans (Finset.prod_dvd_prod_of_dvd ..)
    exact fun s _ => Nat.dvd_add ((Nat.gcd_dvd_left D s).trans hdvd) (Nat.gcd_dvd_right D s)

set_option maxRecDepth 10000 in
theorem residue18 (L : ℕ) : Cover L 18 8 (9*10*12*15*16*18) := by
  apply lift_residue (D := 180) L (by decide)
  decide +kernel

set_option maxRecDepth 10000 in
theorem residue20 (L : ℕ) : Cover L 20 8 (10*12*15*16*18*20) := by
  apply lift_residue (D := 120) L (by decide)
  decide +kernel

end Erdos708Slots
