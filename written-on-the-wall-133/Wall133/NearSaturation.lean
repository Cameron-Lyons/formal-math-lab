import Wall133.RadiusFive

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- A private contact at the j-th positive even index is a neighbor of the
endpoint which touches the path only at the endpoint and that index. -/
def PrivateContact (P : Chain G n) (j : Fin (n/2)) : Prop :=
  ∃ w, G.Adj (P.vertex 0) w ∧ G.Adj (P.vertex (2*j.val+2)) w ∧
    ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) w → i = 2*j.val+2

/-- When a saturated endpoint has at most one fewer neighbor than the number
of possible blocking indices, all except at most two indices have a private
contact. The two exceptional indices can coincide. -/
theorem near_saturation_with_witness [Fintype V] [DecidableRel G.Adj] (P : Chain G n)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 2 ≤ n)
    (hd : n/2 ≤ G.degree (P.vertex 0)+1) (sat : ∀ z, ¬Good P z) :
    ∃ a b : Fin (n/2), (a = b ∨ ∃ w, G.Adj (P.vertex 0) w ∧
      G.Adj (P.vertex (2*a.val+2)) w ∧ G.Adj (P.vertex (2*b.val+2)) w) ∧
      ∀ j, j ≠ a → j ≠ b → PrivateContact P j := by
  classical
  let N := G.neighborFinset (P.vertex 0)
  have ha (z : N) := (G.mem_neighborFinset _ _).mp z.property
  choose f hf using fun z : N => blocker P c hn (ha z) (sat z)
  have inj : Function.Injective f := fun x y he => Subtype.ext
    (unique_at_site P h4 (f x) (ha x) (hf x) (ha y) (he ▸ hf y))
  let A : Finset (Fin (n/2)) := Finset.univ.image f
  have hac : A.card = G.degree (P.vertex 0) := by
    simp [A, Finset.card_image_of_injective _ inj, N, G.card_neighborFinset_eq_degree]
  have hdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  change (Finset.univ \ A).card + A.card = Finset.univ.card at hdiff
  rw [hac, Finset.card_univ, Fintype.card_fin] at hdiff
  have hex : ∃ a : Fin (n/2), ∀ j, j ≠ a → ∃ x : N, f x = j := by
    by_cases ht : (Finset.univ \ A).Nonempty
    · obtain ⟨a,haa⟩ := ht
      refine ⟨a, fun j hja => ?_⟩
      have hj : j ∈ A := by
        by_contra hj
        have hj' : j ∈ Finset.univ \ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩
        exact hja (Finset.card_le_one.mp (by omega : (Finset.univ \ A).card ≤ 1) _ hj' _ haa)
      simpa [A] using hj
    · refine ⟨⟨0, by omega⟩, fun j _ => ?_⟩
      have hj : j ∈ A := by
        by_contra hj
        exact ht ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hj⟩⟩
      simpa [A] using hj
  obtain ⟨a,hother⟩ := hex
  have chooseSecond : ∃ b : Fin (n/2), (a = b ∨ ∃ w, G.Adj (P.vertex 0) w ∧
      G.Adj (P.vertex (2*a.val+2)) w ∧ G.Adj (P.vertex (2*b.val+2)) w) ∧ ∀ x : N,
      G.Adj (P.vertex (2*a.val+2)) x.val → f x = b := by
    by_cases h : ∃ x : N, G.Adj (P.vertex (2*a.val+2)) x.val
    · obtain ⟨x,hx⟩ := h
      exact ⟨f x, Or.inr ⟨x.val,ha x,hx,hf x⟩, fun y hy => congrArg f (Subtype.ext
        (unique_at_site P h4 a (ha y) hy (ha x) hx))⟩
    · exact ⟨a, Or.inl rfl, fun x hx => False.elim (h ⟨x,hx⟩)⟩
  obtain ⟨b,hshared,hsecond⟩ := chooseSecond
  refine ⟨a,b,hshared,fun j hja hjb => ?_⟩
  obtain ⟨x,hx⟩ := hother j hja
  refine ⟨x.val, ha x, hx ▸ hf x, fun i hi hpos hxi => ?_⟩
  have he := P.even_of_common c hi (ha x) hxi
  let k : Fin (n/2) := ⟨i/2-1, by omega⟩
  have hk : i = 2*k.val+2 := by dsimp [k]; omega
  have hcontact : G.Adj (P.vertex (2*k.val+2)) x.val := hk ▸ hxi
  have hka : k ≠ a := fun e => hjb (hx.symm.trans (hsecond x (e ▸ hcontact)))
  obtain ⟨y,hy⟩ := hother k hka
  have heq : x = y := Subtype.ext (unique_at_site P h4 k (ha x) hcontact (ha y) (hy ▸ hf y))
  have hkj := hy.symm.trans ((congrArg f heq).symm.trans hx)
  simpa [hkj] using hk

/-- All but at most two sites have private contacts. -/
theorem near_saturation [Fintype V] [DecidableRel G.Adj] (P : Chain G n)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 2 ≤ n)
    (hd : n/2 ≤ G.degree (P.vertex 0)+1) (sat : ∀ z, ¬Good P z) :
    ∃ a b : Fin (n/2), ∀ j, j ≠ a → j ≠ b → PrivateContact P j := by
  obtain ⟨a,b,_,h⟩ := near_saturation_with_witness P c h4 hn hd sat
  exact ⟨a,b,h⟩

/-- Three disjoint pairs of consecutive indices survive any two exceptions:
at least one pair consists of two private contacts. -/
theorem consecutive_private_contacts [Fintype V] [DecidableRel G.Adj] (P : Chain G n)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 7 ≤ n/2)
    (hd : n/2 ≤ G.degree (P.vertex 0)+1) (sat : ∀ z, ¬Good P z) :
    ∃ j k : Fin (n/2), 1 ≤ j.val ∧ k.val = j.val+1 ∧ PrivateContact P j ∧ PrivateContact P k := by
  obtain ⟨a,b,h⟩ := near_saturation P c h4 (by omega) hd sat
  have ex : ∃ i : ℕ, 1 ≤ i ∧ i+1 < n/2 ∧ i ≠ a.val ∧ i ≠ b.val ∧
      i+1 ≠ a.val ∧ i+1 ≠ b.val := by
    by_contra! hf
    have := hf 1 (by omega) (by omega)
    have := hf 3 (by omega) (by omega)
    have := hf 5 (by omega) (by omega)
    omega
  obtain ⟨i,hi,hik,hai,hbi,hak,hbk⟩ := ex
  exact ⟨⟨i, by omega⟩, ⟨i+1,hik⟩, hi,rfl,
    h _ (fun e => hai (congrArg Fin.val e)) (fun e => hbi (congrArg Fin.val e)),
    h _ (fun e => hak (congrArg Fin.val e)) (fun e => hbk (congrArg Fin.val e))⟩

/-- Among seven consecutive indices, two exceptions spoil at most four of
the six neighboring pairs. A prescribed initial index may also be excluded. -/
theorem private_pair_avoiding [Fintype V] [DecidableRel G.Adj] (P : Chain G n)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 8 ≤ n/2) (avoid : ℕ)
    (hd : n/2 ≤ G.degree (P.vertex 0)+1) (sat : ∀ z, ¬Good P z) :
    ∃ j k : Fin (n/2), 1 ≤ j.val ∧ j.val ≠ avoid ∧ k.val = j.val+1 ∧
      PrivateContact P j ∧ PrivateContact P k := by
  obtain ⟨a,b,h⟩ := near_saturation P c h4 (by omega) hd sat
  have ex : ∃ i : ℕ, 1 ≤ i ∧ i+1 < n/2 ∧ i ≠ avoid ∧ i ≠ a.val ∧ i ≠ b.val ∧
      i+1 ≠ a.val ∧ i+1 ≠ b.val := by
    by_contra! hf
    have h1 := hf 1 (by omega) (by omega)
    have h2 := hf 2 (by omega) (by omega)
    have h3 := hf 3 (by omega) (by omega)
    have h4 := hf 4 (by omega) (by omega)
    have h5 := hf 5 (by omega) (by omega)
    have h6 := hf 6 (by omega) (by omega)
    omega
  obtain ⟨i,hi,hik,he,hai,hbi,hak,hbk⟩ := ex
  exact ⟨⟨i, by omega⟩, ⟨i+1,hik⟩, hi, he,rfl,
    h _ (fun e => hai (congrArg Fin.val e)) (fun e => hbi (congrArg Fin.val e)),
    h _ (fun e => hak (congrArg Fin.val e)) (fun e => hbk (congrArg Fin.val e))⟩

end Wall133
