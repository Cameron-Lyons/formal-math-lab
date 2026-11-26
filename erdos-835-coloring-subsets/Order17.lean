module

public import Cyclic

@[expose] public section

namespace Erdos835

open Finset Equiv.Perm

/-- The two families of exact-one constraints in the 20-point search.
The selected quadruples must cover every triple once and must meet each
orbit of quadruples once. -/
structure QuadrupleSeed {V : Type*} (W : Finset V)
    (translate : Fin 17 → Finset V → Finset V) (D : Finset V → Prop) : Prop where
  blocks : ∀ Q, D Q → Q ⊆ W ∧ Q.card = 4
  triples : ∀ T ⊆ W, T.card = 3 → ∃! Q, D Q ∧ T ⊆ Q
  orbits : ∀ Q ⊆ W, Q.card = 4 → ∃! j : Fin 17, D (translate j Q)

abbrev CyclicQuadrupleSeed (W : Finset Point) (g : Equiv.Perm Point) :=
  QuadrupleSeed W (fun j Q => Q.map (g ^ j.val).toEmbedding)

private theorem stable_of_support_subset {g : Equiv.Perm Point} {W : Finset Point}
    (hs : g.support ⊆ W) (n : ℕ) : W.map (g ^ n).toEmbedding = W := by
  apply map_eq_of_subset
  intro x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  by_cases hm : y ∈ g.support
  · exact hs (pow_apply_mem_support.mpr hm)
  · simpa only [Equiv.coe_toEmbedding, pow_apply_eq_self_of_apply_eq_self (notMem_support.mp hm)]
      using hy

/-- Following the faces of the 17-cycle follows all seventeen colors. -/
theorem order17_palette_orbit {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hg : orderOf g = 17) (i : Fin 17) :
    Function.Bijective (fun j : Fin 17 => (τ ^ j.val) i) := by
  have gc := isCycle_of_prime_order' (σ := g) (hg ▸ (by decide : Nat.Prime 17))
    (by rw [hg]; decide)
  have hA : g.support.card = 17 := gc.orderOf.symm.trans hg
  have hf := face_bijective hc g.support hA
  have moved (a : Fin 17) : τ a ≠ a := by
    obtain ⟨x, hx⟩ := hf.2 a
    let y : g.support := ⟨g x, apply_mem_support.mpr x.property⟩
    have hgS : g.support.map g.toEmbedding = g.support := by
      simpa using stable_of_support_subset (g := g) (Subset.rfl : g.support ⊆ g.support) 1
    have hmap : (face g.support hA x).val.map g.toEmbedding = (face g.support hA y).val := by
      simp [face, hgS, y]
    have hy : c (face g.support hA y) = τ a :=
      (congrArg c (Subtype.ext hmap.symm)).trans ((he _).trans (congrArg τ hx))
    intro e
    exact (mem_support.mp x.property) (congrArg (fun t : g.support => t.val) (hf.1 (hy.trans (e.trans hx.symm))))
  have hd := orderOf_dvd_of_pow_eq_one (palette_pow_eq_one hc he (hg ▸ pow_orderOf_eq_one g))
  have ht : orderOf τ = 17 := ((by decide : Nat.Prime 17).eq_one_or_self_of_dvd _ hd).resolve_left
    (fun h => moved i (by rw [orderOf_eq_one_iff.mp h]; rfl))
  have tc := isCycle_of_prime_order' (σ := τ) (by rw [ht]; decide)
    (by rw [ht]; decide)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  refine ⟨?_, rfl⟩
  intro a
  have along : τ.SameCycle i a := tc.exists_zpow_eq (moved i) (moved a)
  obtain ⟨j, hj, ha⟩ := along.exists_pow_eq'
  exact ⟨⟨j, ht ▸ hj⟩, ha⟩

/-- An order-17 symmetry of a full rainbow coloring forces a solution of
the local exact-cover problem on the cycle and any three fixed points. -/
theorem order17_forces_quadruple_seed {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hg : orderOf g = 17) (W : Finset Point) (hW : W.card = 20) (hs : g.support ⊆ W) :
    ∃ D, CyclicQuadrupleSeed W g D := by
  let D (Q : Finset Point) := Q ⊆ W ∧ Q.card = 4 ∧
    ∃ h : (W \ Q).card = 16, c ⟨_, h⟩ = 0
  refine ⟨D, ⟨fun _ h => ⟨h.1, h.2.1⟩, ?_, ?_⟩⟩
  · intro T hT h3
    let A := W \ T
    have hA : A.card = 17 := by rw [card_sdiff_of_subset hT, hW, h3]
    have hf := face_bijective hc A hA
    have extension (x : A) : D (insert x.val T) ↔ c (face A hA x) = 0 := by
      obtain ⟨hxW, hxT⟩ := mem_sdiff.mp x.property
      have hsub := insert_subset hxW hT
      have h4 : (insert x.val T).card = 4 := by simp [hxT, h3]
      have hcard : (W \ insert x.val T).card = 16 := by rw [card_sdiff_of_subset hsub, hW, h4]
      have heq : (⟨_, hcard⟩ : Block) = face A hA x := Subtype.ext (sdiff_insert W T x.val)
      exact ⟨fun h => (congrArg c heq).symm.trans h.2.2.choose_spec,
        fun h => ⟨hsub, h4, hcard, (congrArg c heq).trans h⟩⟩
    obtain ⟨x, hx⟩ := hf.2 0
    refine ⟨insert x.val T, ⟨(extension x).mpr hx, subset_insert _ _⟩, ?_⟩
    rintro Q ⟨hQ, hTQ⟩
    obtain ⟨y, hy, rfl⟩ := exists_eq_insert_iff.mpr ⟨hTQ, by rw [h3, hQ.2.1]⟩
    let z : A := ⟨y, mem_sdiff.mpr ⟨hQ.1 (mem_insert_self _ _), hy⟩⟩
    exact congrArg (fun t : A => insert t.val T) (hf.1 (((extension z).mp hQ).trans hx.symm))
  · intro Q hQ h4
    let B : Block := ⟨W \ Q, by rw [card_sdiff_of_subset hQ, hW, h4]⟩
    have orbit (j : Fin 17) : D (Q.map (g ^ j.val).toEmbedding) ↔ (τ ^ j.val) (c B) = 0 := by
      let f := (g ^ j.val).toEmbedding
      have stable : W.map f = W := stable_of_support_subset hs _
      have incl : Q.map f ⊆ W := stable ▸ map_subset_map.mpr hQ
      have hsize : (Q.map f).card = 4 := (card_map _).trans h4
      have hdiff : (W \ Q.map f).card = 16 := by rw [card_sdiff_of_subset incl, hW, hsize]
      have hb : B.val.map f = W \ Q.map f := by
        change (W \ Q).map f = _
        rw [map_sdiff, stable]
      have hcolor : c ⟨_, hdiff⟩ = (τ ^ j.val) (c B) :=
        (congrArg c (Subtype.ext hb.symm)).trans (equivariant_pow he j.val B)
      exact ⟨fun h => hcolor.symm.trans h.2.2.choose_spec,
        fun h => ⟨incl, hsize, hdiff, hcolor.trans h⟩⟩
    have hf := order17_palette_orbit hc he hg (c B)
    obtain ⟨j, hj⟩ := hf.2 0
    exact ⟨j, (orbit j).mpr hj, fun k hk => hf.1 (((orbit k).mp hk).trans hj.symm)⟩

/-- Such a 20-set always exists on 32 points. -/
theorem order17_has_quadruple_seed {c g τ} (hc : Rainbow c) (he : Equivariant c g τ)
    (hg : orderOf g = 17) :
    ∃ (W : Finset Point) (D : Finset Point → Prop),
      W.card = 20 ∧ g.support ⊆ W ∧ g.support.card = 17 ∧ CyclicQuadrupleSeed W g D := by
  have gc := isCycle_of_prime_order' (σ := g) (hg ▸ (by decide : Nat.Prime 17))
    (by rw [hg]; decide)
  have hcard := gc.orderOf.symm.trans hg
  obtain ⟨W, hs, _, hW⟩ := exists_subsuperset_card_eq (subset_univ g.support)
    (show g.support.card ≤ 20 by omega) (by decide : 20 ≤ Fintype.card Point)
  obtain ⟨D, hD⟩ := order17_forces_quadruple_seed hc he hg W hW hs
  exact ⟨W, D, hW, hs, hcard, hD⟩

end Erdos835
