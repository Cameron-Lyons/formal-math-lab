module

public import Mathlib.GroupTheory.Perm.Cycle.Type

@[expose] public section

namespace Erdos835

open Finset Equiv.Perm

/-- For the two primes in the indicated interval, there is an invariant 18-set
containing exactly one nontrivial cycle. -/
theorem primeOrder_witness18 {p : ℕ} (hp : p.Prime) (lo : 11 ≤ p) (hi : p ≤ 14)
    (g : Equiv.Perm (Fin 32)) (hg : orderOf g = p) :
    ∃ W : Finset (Fin 32), W.card = 18 ∧ W.map g.toEmbedding = W ∧
      (W.filter fun x => g x = x).card = 18 - p := by
  classical
  -- Every nontrivial cycle has length p, so there are at most two such cycles.
  obtain ⟨n, hn⟩ := cycleType_prime_order (hg ▸ hp : (orderOf g).Prime)
  have hsize := g.sum_cycleType
  rw [hn, hg, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hsize
  have bound := g.support.card_le_univ
  simp only [Fintype.card_fin] at bound
  have two : n + 1 ≤ 2 := by
    by_contra! hn'
    have hh := Nat.mul_le_mul hn' lo
    omega
  have hfixed : 18 - p ≤ g.supportᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    have h := Nat.mul_le_mul_right p two
    omega
  obtain ⟨F, hF, hFcard⟩ := Finset.exists_subset_card_eq hfixed
  have fixed {x} (hx : x ∈ F) : g x = x := notMem_support.mp (mem_compl.mp (hF hx))
  -- Pick one cycle explicitly and adjoin the selected fixed points.
  have gne : g ≠ 1 := by
    intro h
    simp [h] at hg
    omega
  obtain ⟨x, hx⟩ : ∃ x, g x ≠ x := by
    by_contra! h
    exact gne (Equiv.ext h)
  let A := (g.cycleOf x).support
  have ac := g.isCycle_cycleOf hx
  have orderA := (hp.eq_one_or_self_of_dvd _ (hg ▸ g.orderOf_cycleOf_dvd_orderOf x)).resolve_left
    (fun h => hx ((g.cycleOf_eq_one_iff).mp (orderOf_eq_one_iff.mp h)))
  have cardA : A.card = p := ac.orderOf.symm.trans orderA
  have moved {y} (hy : y ∈ A) : g y ≠ y := mem_support.mp (g.support_cycleOf_le x hy)
  have stable {y} (hy : y ∈ A) : g y ∈ A := (mem_support_cycleOf_iff' hx).mpr
    (sameCycle_apply_right.mpr ((mem_support_cycleOf_iff' hx).mp hy))
  have dis : Disjoint A F := Finset.disjoint_left.mpr fun y hy hF' => moved hy (fixed hF')
  refine ⟨A ∪ F, ?_, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint dis, hFcard, cardA]
    omega
  · apply Finset.map_eq_of_subset
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hy
    rcases Finset.mem_union.mp hz with ha | hf
    · exact Finset.mem_union_left _ (stable ha)
    · exact Finset.mem_union_right _ (by simpa [fixed hf] using hf)
  · have heq : (A ∪ F).filter (fun y => g y = y) = F := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_union]
      exact ⟨fun ⟨h, hy⟩ => h.resolve_left (fun ha => moved ha hy), fun h => ⟨Or.inr h, fixed h⟩⟩
    rw [heq, hFcard]

private theorem proper_divisor32_dvd16 {d : ℕ} (hd : d ∣ 32) (h : d ≠ 32) : d ∣ 16 := by
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 5)).mp hd
  have hi' : i ≠ 5 := fun e => h (by rw [e]; decide)
  exact pow_dvd_pow 2 (show i ≤ 4 by omega)

/-- A permutation of 17 colors whose 32nd power is trivial has trivial 16th power. -/
theorem palette_pow16 (τ : Equiv.Perm (Fin 17)) (h : τ ^ 32 = 1) : τ ^ 16 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← τ.lcm_cycleType, Multiset.lcm_dvd]
  intro d hd
  apply proper_divisor32_dvd16 ((dvd_of_mem_cycleType hd).trans (orderOf_dvd_of_pow_eq_one h))
  have small := (le_card_support_of_mem_cycleType hd).trans τ.support.card_le_univ
  simp only [Fintype.card_fin] at small
  omega

/-- Choose any `r` pairs from a fixed-point-free involution on 32 points. -/
private theorem stable_pairs (t : Equiv.Perm (Fin 32)) (hinv : ∀ x, t (t x) = x)
    (hfree : ∀ x, t x ≠ x) (r : ℕ) (hr : r ≤ 16) :
    ∃ W : Finset (Fin 32), W.card = 2 * r ∧ ∀ x ∈ W, t x ∈ W := by
  classical
  induction r with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ r ih =>
    obtain ⟨W, hc, hs⟩ := ih (by omega)
    have hlt : W.card < (univ : Finset (Fin 32)).card := by simp [hc]; omega
    obtain ⟨x, _, hx⟩ := exists_mem_notMem_of_card_lt_card hlt
    have htx : t x ∉ W := fun h => hx (hinv x ▸ hs _ h)
    refine ⟨insert (t x) (insert x W), ?_, ?_⟩
    · rw [card_insert_of_notMem (by simp [htx, hfree x]), card_insert_of_notMem hx, hc]
      omega
    · intro y hy
      simp only [mem_insert] at hy ⊢
      rcases hy with rfl | rfl | hy
      · exact Or.inr (Or.inl (hinv _))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (hs _ hy))

/-- Nine transposed pairs form an invariant 18-set. -/
theorem involution_witness18 (g : Equiv.Perm (Fin 32)) (hinv : ∀ x, g (g x) = x)
    (hfree : ∀ x, g x ≠ x) :
    ∃ W : Finset (Fin 32), W.card = 18 ∧ W.map g.toEmbedding = W := by
  obtain ⟨W, hW, hs⟩ := stable_pairs g hinv hfree 9 (by decide)
  refine ⟨W, hW, Finset.map_eq_of_subset ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
  exact hs z hz

/-- The half-turn of a permutation of order 32 on 32 points is fixed-point-free
and stabilizes a set of 18 points. -/
theorem order32_witness18 (g : Equiv.Perm (Fin 32)) (hg : orderOf g = 32) :
    ∃ W : Finset (Fin 32), W.card = 18 ∧ W.map (g ^ 16).toEmbedding = W ∧
      ∀ x, (g ^ 16) x ≠ x := by
  classical
  have full : 32 ∈ g.cycleType := by
    by_contra h
    have absurdDvd : orderOf g ∣ 16 := by
      rw [← g.lcm_cycleType, Multiset.lcm_dvd]
      intro d hd
      apply proper_divisor32_dvd16 (hg ▸ dvd_of_mem_cycleType hd)
      exact fun eq => h (eq ▸ hd)
    rw [hg] at absurdDvd
    exact (by decide : ¬32 ∣ 16) absurdDvd
  have htype := cycleType_of_card_le_mem_cycleType_add_two (by decide) full
  have hc : g.IsCycle := card_cycleType_eq_one.mp (by simp [htype])
  have supp : g.support = univ := g.support.eq_univ_of_card (by rw [← g.sum_cycleType, htype]; simp)
  have hsupp := hc.support_pow_of_pos_of_lt_orderOf (by decide : 0 < 16) (by rw [hg]; decide)
  have hfree (x) : (g ^ 16) x ≠ x := mem_support.mp (by rw [hsupp, supp]; exact mem_univ x)
  have hinv (x) : (g ^ 16) ((g ^ 16) x) = x := by
    rw [← Equiv.Perm.mul_apply, ← pow_add, show 16 + 16 = orderOf g by omega, pow_orderOf_eq_one]
    rfl
  obtain ⟨W, hW, hmap⟩ := involution_witness18 _ hinv hfree
  exact ⟨W, hW, hmap, hfree⟩

end Erdos835
