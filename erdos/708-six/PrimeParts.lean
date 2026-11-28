module

public import Slots
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

@[expose] public section

namespace Erdos708Slots

theorem Cover.mono {L M k k' t t' : ℕ} (h : Cover L M k t) (hk : k ≤ k') (ht : t' ∣ t) :
    Cover L M k' t' := by
  obtain ⟨B, hB, hc, hd⟩ := h
  exact ⟨B, hB, hc.trans hk, dvd_trans ht hd⟩

/-- Append all factors when each has at least the final budget's worth of multiples. -/
theorem extend_factors {L M k cap t : ℕ} (factors : List ℕ) (h : Cover L M k t)
    (hbudget : k + factors.length ≤ cap)
    (hsmall : ∀ d ∈ factors, 0 < d ∧ cap*d ≤ M) :
    Cover L M (k + factors.length) (t*factors.prod) := by
  induction factors generalizing k t with
  | nil => simpa
  | cons d ds ih =>
    obtain ⟨hd, hcap⟩ := hsmall d (by simp)
    have hk : k+1 ≤ cap := by simp only [List.length_cons] at hbudget; omega
    have hnext := extend_small h hd ((Nat.mul_le_mul_right d hk).trans hcap)
    have hrest := ih hnext (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbudget)
      (fun v hv => hsmall v (by simp [hv]))
    simpa [Nat.mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

/-- If two covers intersect, their union pays the lcm, and the saved site can be used
along with the spare budget to pay any list of small factors covering the gcd. -/
theorem overlapRepair {L M i j cap t u : ℕ} (ht : Cover L M i t) (hu : Cover L M j u)
    (factors : List ℕ) (hcount : i+j ≤ cap) (hroom : i+j+factors.length ≤ cap+1)
    (hsmall : ∀ d ∈ factors, 0 < d ∧ cap*d ≤ M) (hgcd : t.gcd u ∣ factors.prod) :
    Cover L M cap (t*u) := by
  obtain ⟨U, hU, hUc, hUd⟩ := ht
  obtain ⟨V, hV, hVc, hVd⟩ := hu
  have hwindow := Finset.union_subset hU hV
  have hcard := Finset.card_union_le U V
  by_cases hd : Disjoint U V
  · refine ⟨U ∪ V, hwindow, by omega, ?_⟩
    rw [Finset.prod_union hd]
    exact Nat.mul_dvd_mul hUd hVd
  · have hne := mt Finset.card_union_eq_card_add_card.mp hd
    have hbudget : (U ∪ V).card + factors.length ≤ cap := by omega
    have hA := dvd_trans hUd (Finset.prod_dvd_prod_of_subset U (U ∪ V) id Finset.subset_union_left)
    have hB := dvd_trans hVd (Finset.prod_dvd_prod_of_subset V (U ∪ V) id Finset.subset_union_right)
    have hboth : Cover L M (U ∪ V).card (t.lcm u) := ⟨_, hwindow, le_rfl, Nat.lcm_dvd hA hB⟩
    apply (extend_factors factors hboth hbudget hsmall).mono hbudget
    simpa only [Nat.lcm_mul_gcd] using Nat.mul_dvd_mul_left (t.lcm u) hgcd

/-- Lift a cover in a quotient interval to exactly `d` multiples of `p` in the
original interval. Padding before lifting supplies all `d` copies of `p`. -/
theorem liftCover {L M d p n target : ℕ} (hp : 0 < p) (hfit : p*n ≤ M) (hcnt : d ≤ n)
    (hlocal : ∀ K, Cover K n d target) : Cover L M d (p^d*target) := by
  let K := (L+p-1)/p
  have hstart : L ≤ p*K ∧ p*K < L+p := by
    have h₁ := Nat.div_add_mod (L+p-1) p
    have h₂ := Nat.mod_lt (L+p-1) hp
    dsimp [K]
    omega
  obtain ⟨U, hU, hUc, hUd⟩ := hlocal K
  obtain ⟨V, hUV, hV, hVc⟩ := Finset.exists_subsuperset_card_eq hU hUc
    (show d ≤ (Finset.Ico K (K+n)).card by simpa using hcnt)
  let f := fun v => p*v
  have hinj : Function.Injective f := fun _ _ h => Nat.eq_of_mul_eq_mul_left hp h
  refine ⟨V.image f, ?_, by rw [Finset.card_image_of_injective V hinj, hVc], ?_⟩
  · intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (hV hv)
    have hleft := Nat.mul_le_mul_left p hlo
    have hright := Nat.mul_le_mul_left p (show v+1 ≤ K+n from hhi)
    simp only [Nat.mul_add, Nat.mul_one] at hright
    apply Finset.mem_Ico.mpr
    dsimp [f]
    omega
  · rw [Finset.prod_image hinj.injOn]
    change p^d*target ∣ ∏ x ∈ V, (fun _ : ℕ => p) x * (fun a : ℕ => a) x
    rw [Finset.prod_mul_distrib, Finset.prod_const, hVc]
    exact Nat.mul_dvd_mul_left _ (dvd_trans hUd (Finset.prod_dvd_prod_of_subset U V id hUV))

end Erdos708Slots
