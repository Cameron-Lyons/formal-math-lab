import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.GCD.Basic

/-! Extending an interval product cover, including when the new modulus already divides
an occupied site. The latter argument is the cumulative-gcd step in C. Bergström,
*Exact Small-n Values and Constructive Lower Bounds for Erdős Problem 708* (2026). -/
namespace Erdos708Slots

/-- The target divides the product of at most `k` distinct natural numbers in `[L,L+M)`. -/
def Cover (L M k target : ℕ) : Prop :=
  ∃ B : Finset ℕ, B ⊆ Finset.Ico L (L + M) ∧ B.card ≤ k ∧ target ∣ ∏ b ∈ B, b

/-- If the window fits `k+1` full blocks of length `d`, some multiple of `d` is unused. -/
theorem fresh_multiple (L M k d : ℕ) (B : Finset ℕ) (hB : B.card ≤ k)
    (hd : 0 < d) (hcap : (k+1)*d ≤ M) :
    ∃ b ∈ Finset.Ico L (L+M), b ∉ B ∧ d ∣ b := by
  let base := d * ((L+d-1)/d)
  have hbase : L ≤ base ∧ base < L + d := by
    have h₁ := Nat.div_add_mod (L+d-1) d
    have h₂ := Nat.mod_lt (L+d-1) hd
    dsimp [base]
    omega
  let site := fun (i : ℕ) => base + i*d
  have hinj : Function.Injective site := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hij)
  have hcard : B.card < ((Finset.range (k+1)).image site).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    omega
  obtain ⟨b, hb, hout⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hb
  have hidx : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have himul := Nat.mul_le_mul_right d hidx
  have hend : k*d + d ≤ M := by simpa [Nat.add_mul] using hcap
  refine ⟨_, Finset.mem_Ico.mpr ⟨by dsimp [site]; omega, by dsimp [site]; omega⟩, hout, ?_⟩
  exact Nat.dvd_add (Nat.dvd_mul_right d _) (Nat.dvd_mul_left d i)

private theorem insert_site {L M k target : ℕ} {B : Finset ℕ} {b : ℕ}
    (hB : B ⊆ Finset.Ico L (L+M)) (hcard : B.card ≤ k)
    (hb : b ∈ Finset.Ico L (L+M)) (hnew : b ∉ B)
    (hp : target ∣ (∏ a ∈ B, a) * b) : Cover L M (k+1) target := by
  refine ⟨insert b B, Finset.insert_subset_iff.mpr ⟨hb, hB⟩,
    (Finset.card_insert_le b B).trans (Nat.add_le_add_right hcard 1), ?_⟩
  simpa [Finset.prod_insert hnew, Nat.mul_comm] using hp

/-- A small gcd suffices even if the new modulus is large and its multiple is occupied. -/
theorem extend_gcd {L M k target d : ℕ} (h : Cover L M k target) (hpos : 0 < d)
    (hd : d ≤ M) (hcap : (k+1) * target.gcd d ≤ M) :
    Cover L M (k+1) (target*d) := by
  obtain ⟨B, hB, hcard, hpaid⟩ := h
  obtain ⟨b, hb, _, hdb⟩ := fresh_multiple L M 0 d ∅ (by simp) hpos (by simpa using hd)
  by_cases hmem : b ∈ B
  · have hdiv : b ∣ ∏ a ∈ B, a := by
      rw [← B.prod_erase_mul (fun a => a) hmem]
      exact Nat.dvd_mul_left _ _
    have hlcm := Nat.lcm_dvd hpaid (dvd_trans hdb hdiv)
    obtain ⟨c, hc, hcnew, hgc⟩ := fresh_multiple L M k (target.gcd d) B hcard
      (Nat.gcd_pos_of_pos_right target hpos) hcap
    apply insert_site hB hcard hc hcnew
    simpa only [Nat.lcm_mul_gcd] using Nat.mul_dvd_mul hlcm hgc
  · exact insert_site hB hcard hb hmem (Nat.mul_dvd_mul hpaid hdb)

/-- A modulus with enough multiples can be appended to any existing cover. -/
theorem extend_small {L M k target d : ℕ} (h : Cover L M k target) (hpos : 0 < d)
    (hcap : (k+1)*d ≤ M) : Cover L M (k+1) (target*d) := by
  obtain ⟨B, hB, hcard, hpaid⟩ := h
  obtain ⟨b, hb, hnew, hd⟩ := fresh_multiple L M k d B hcard hpos hcap
  exact insert_site hB hcard hb hnew (Nat.mul_dvd_mul hpaid hd)

/-- A modulus factored as `u*v` can be paid at the cost of two additional sites. -/
theorem extend_two {L M k target u v : ℕ} (h : Cover L M k target)
    (hu : 0 < u) (hv : 0 < v) (hucap : (k+1)*u ≤ M) (hvcap : (k+2)*v ≤ M) :
    Cover L M (k+2) (target*(u*v)) := by
  simpa only [Nat.mul_assoc] using extend_small (extend_small h hu hucap) hv hvcap

/-- A finite schedule of multiplicative targets. Every row stores the modulus of a
new factor. Each successful step applies the cumulative gcd extension theorem. -/
def slotOK (M : ℕ) : ℕ → ℕ → List ℕ → Bool
  | _, _, [] => true
  | k, t, d :: ds => 0 < d && d ≤ M && (k+1)*t.gcd d ≤ M && slotOK M (k+1) (t*d) ds

theorem slotOK_sound {L M : ℕ} (ds : List ℕ) {k t : ℕ} (h : Cover L M k t)
    (hc : slotOK M k t ds) : Cover L M (k+ds.length) (t*ds.prod) := by
  induction ds generalizing k t with
  | nil => simpa using h
  | cons d ds ih =>
    obtain ⟨⟨⟨hd, hm⟩, hg⟩, hrest⟩ := by simpa [slotOK] using hc
    have res := ih (extend_gcd h hd hm hg) hrest
    simpa [Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using res

end Erdos708Slots
