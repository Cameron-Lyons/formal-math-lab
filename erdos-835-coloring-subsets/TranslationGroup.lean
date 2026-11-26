module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Erdos835

open Finset MulAction

/-- A point in a smaller set has a nontrivial stabilizer. -/
private theorem nontrivial_stabilizer {G X : Type*} [Group G] [Fintype G] [MulAction G X]
    [Fintype X] (x : X) (hs : Fintype.card X < Fintype.card G) :
    ∃ g : G, g ≠ 1 ∧ g • x = x := by
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt (· • x : G → X) hs
  exact ⟨a⁻¹ * b, (fun he => hab (inv_mul_eq_one.mp he)), by rw [mul_smul, ← h, inv_smul_smul]⟩

/-- In an abelian group action, fixing one point of an orbit fixes every point of it. -/
private theorem fixes_whole_orbit {G X : Type*} [CommGroup G] [MulAction G X]
    (q : orbitRel.Quotient G X) (x : q.orbit) {g : G} (hx : g • x = x) :
    q.orbit ⊆ fixedBy X g := by
  intro y hy
  obtain ⟨z, hz⟩ := exists_smul_eq G x (⟨y, hy⟩ : q.orbit)
  have h : g • (z • x) = z • x := by rw [← mul_smul, mul_comm, mul_smul, hx]
  rw [hz] at h
  exact congrArg Subtype.val h

/-- A nonidentity element of any abelian group of order 32 acting on 17 colors
fixes at least eight of the colors. -/
theorem many_fixed_colors {G : Type*} [CommGroup G] [Fintype G] (hG : Fintype.card G = 32)
    (ρ : G →* Equiv.Perm (Fin 17)) :
    ∃ g : G, g ≠ 1 ∧ 8 ≤ (Finset.univ.filter fun a => ρ g a = a).card := by
  classical
  let X := Fin 17
  let _ : MulAction G X := MulAction.compHom X ρ
  let Q := orbitRel.Quotient G X
  let _ : Fintype Q := Fintype.ofFinite Q
  let size (q : Q) := Fintype.card q.orbit
  let fixed (g : G) := Fintype.card (fixedBy X g)
  have hf (g : G) : fixed g = (Finset.univ.filter fun a => ρ g a = a).card := by
    exact Fintype.card_subtype (fun a => ρ g a = a)
  by_contra! H
  have small (g : G) (hg : g ≠ 1) : fixed g ≤ 7 := by have := H g hg; rw [← hf] at this; omega
  have size_le (q : Q) : size q ≤ 17 := Fintype.card_subtype_le _
  have small_orbit (q : Q) : size q ≤ 7 := by
    obtain ⟨x, hx⟩ := q.nonempty_orbit
    obtain ⟨g, hne, hfix⟩ := nontrivial_stabilizer (G := G) (⟨x, hx⟩ : q.orbit)
      (by change size q < _; have := size_le q; omega)
    have hsub := fixes_whole_orbit q _ hfix
    have hs := card_le_card (Set.toFinset_subset_toFinset.mpr hsub)
    simp only [Set.toFinset_card] at hs
    exact hs.trans (small g hne)
  have sizes (q : Q) : size q = 4 ∨ size q ≤ 2 := by
    have hd : size q ∣ 32 := by
      change Fintype.card q.orbit ∣ 32
      rw [q.orbit_eq_orbit_out Quotient.out_eq', ← hG,
        ← card_orbit_mul_card_stabilizer_eq_card_group G q.out]
      exact Nat.dvd_mul_right _ _
    have h := small_orbit q
    generalize size q = d at *
    interval_cases d <;> omega
  -- Burnside's lemma bounds the number of orbits when every nonidentity element fixes ≤ 7 colors.
  have burn : (∑ g : G, fixed g) = Fintype.card Q * 32 := by
    simpa only [hG] using sum_card_fixedBy_eq_card_orbits_mul_card_group G X
  have hsum := (univ.erase (1 : G)).sum_le_card_nsmul fixed 7
    (fun g hg => small g (mem_erase.mp hg).1)
  have hsplit := univ.sum_erase_add fixed (mem_univ (1 : G))
  have hone : fixed (1 : G) = 17 := by rw [hf]; simp
  rw [card_erase_of_mem (mem_univ _), card_univ, hG] at hsum
  simp only [nsmul_eq_mul] at hsum
  rw [hone, burn] at hsplit
  change (univ.erase (1 : G)).sum fixed + 17 = Fintype.card Q * 32 at hsplit
  change (univ.erase (1 : G)).sum fixed ≤ 217 at hsum
  have hQ : Fintype.card Q ≤ 7 := by omega
  -- The 17 colors cannot fit into seven or fewer orbits with at most one orbit of size four.
  have total : (∑ q : Q, size q) = 17 := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, size, X, Q] using
      (Fintype.card_congr (selfEquivSigmaOrbits' G X)).symm
  let fours := univ.filter fun q : Q => size q = 4
  have two : 1 < fours.card := by
    by_contra! h
    let rest := univ.filter fun q : Q => size q ≠ 4
    have hs := sum_filter_add_sum_filter_not (univ : Finset Q) (fun q => size q = 4) size
    have h1 := fours.sum_le_card_nsmul size 4 (fun _ h => (mem_filter.mp h).2.le)
    have h2 := rest.sum_le_card_nsmul size 2
      (fun q h => (sizes q).resolve_left (mem_filter.mp h).2)
    have count : fours.card + rest.card = Fintype.card Q := univ.card_filter_add_card_filter_not _
    simp only [nsmul_eq_mul, Nat.cast_id] at h1 h2
    rw [total] at hs
    change fours.sum size + rest.sum size = 17 at hs
    omega
  obtain ⟨a, b, ha, hb, hne⟩ := one_lt_card_iff.mp two
  have h4a := (mem_filter.mp ha).2
  have h4b := (mem_filter.mp hb).2
  -- A pair of representatives has at most 16 images, so some nonidentity element fixes both orbits.
  obtain ⟨x, hx⟩ := a.nonempty_orbit
  obtain ⟨y, hy⟩ := b.nonempty_orbit
  have hprod : Fintype.card (a.orbit × b.orbit) < Fintype.card G := by
    rw [Fintype.card_prod, hG]; change size a * size b < 32; rw [h4a, h4b]; decide
  obtain ⟨g, hg, hgxy⟩ := nontrivial_stabilizer (G := G)
    ((⟨x, hx⟩, ⟨y, hy⟩) : a.orbit × b.orbit) hprod
  have hfa := fixes_whole_orbit a _ (congrArg Prod.fst hgxy)
  have hfb := fixes_whole_orbit b _ (congrArg Prod.snd hgxy)
  have hdis : Disjoint a.orbit.toFinset b.orbit.toFinset := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact hne ((orbitRel.Quotient.mem_orbit.mp (Set.mem_toFinset.mp hz)).symm.trans
      (orbitRel.Quotient.mem_orbit.mp (Set.mem_toFinset.mp hz')))
  have hs := card_le_card (Finset.union_subset (Set.toFinset_subset_toFinset.mpr hfa)
    (Set.toFinset_subset_toFinset.mpr hfb))
  rw [card_union_of_disjoint hdis] at hs
  simp only [Set.toFinset_card] at hs
  change size a + size b ≤ fixed g at hs
  have := small g hg
  omega

end Erdos835
