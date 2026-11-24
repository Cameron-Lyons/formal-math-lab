import Wall133.NearSaturation

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj] {n : ℕ}

/-- In a saturated path there are at most twice as many nonprivate blocking
sites as there are sites in excess of the endpoint degree. -/
theorem private_contact_exceptions (P : Chain G n) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hn : 2 ≤ n) {s : ℕ} (hd : n/2 ≤ G.degree (P.vertex 0)+s)
    (sat : ∀ z, ¬Good P z) :
    ∃ B : Finset (Fin (n/2)), B.card ≤ 2*s ∧ ∀ j ∉ B, PrivateContact P j := by
  classical
  let N := G.neighborFinset (P.vertex 0)
  have ha (z : N) := (G.mem_neighborFinset _ _).mp z.property
  choose f hf using fun z : N => blocker P c hn (ha z) (sat z)
  have inj : Function.Injective f := fun x y he =>
    Subtype.ext (unique_at_site P h4 (f x) (ha x) (hf x) (ha y) (he ▸ hf y))
  let A := Finset.univ.image f
  let M := Finset.univ \ A
  have hac : A.card = G.degree (P.vertex 0) := by
    simp [A, Finset.card_image_of_injective _ inj, N, G.card_neighborFinset_eq_degree]
  have hdiff := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  change M.card + A.card = Finset.univ.card at hdiff
  rw [hac,Finset.card_univ,Fintype.card_fin] at hdiff
  let hitting (j : Fin (n/2)) := Finset.univ.filter fun z : N => G.Adj (P.vertex (2*j.val+2)) z.val
  let C := M.biUnion hitting
  have hits (j) : (hitting j).card ≤ 1 := Finset.card_le_one.mpr fun x hx y hy =>
    Subtype.ext (unique_at_site P h4 j (ha x) (Finset.mem_filter.mp hx).2 (ha y)
      (Finset.mem_filter.mp hy).2)
  have hC : C.card ≤ M.card := calc
    _ ≤ ∑ j ∈ M, (hitting j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ M, 1 := Finset.sum_le_sum fun j _ => hits j
    _ = _ := by simp
  let B := M ∪ C.image f
  have hB := Finset.card_union_le M (C.image f)
  have hI := Finset.card_image_le (s := C) (f := f)
  refine ⟨B,by dsimp [B]; omega,?_⟩
  intro j hgood
  have join (i : Fin (n/2)) (hi : i ∉ M) : ∃ z : N, f z = i := by
    by_contra! h
    exact hi (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,by simpa [A] using h⟩)
  obtain ⟨x,hx⟩ := join j (fun h => hgood (Finset.mem_union_left _ h))
  refine ⟨x.val,ha x,hx ▸ hf x,fun i hi hi0 hxi => ?_⟩
  have he := P.even_of_common c hi (ha x) hxi
  let k : Fin (n/2) := ⟨i/2-1,by omega⟩
  have hk : i = 2*k.val+2 := by dsimp [k]; omega
  have hcontact : G.Adj (P.vertex (2*k.val+2)) x.val := hk ▸ hxi
  have hkm : k ∉ M := by
    intro hkM
    have hxC : x ∈ C := Finset.mem_biUnion.mpr ⟨k,hkM,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcontact⟩⟩
    exact hgood (Finset.mem_union_right _ (hx ▸ Finset.mem_image_of_mem f hxC))
  obtain ⟨y,hy⟩ := join k hkm
  have heq : x = y := Subtype.ext (unique_at_site P h4 k (ha x) hcontact (ha y) (hy ▸ hf y))
  have hkj := hy.symm.trans ((congrArg f heq).symm.trans hx)
  simpa [hkj] using hk

/-- Among a family of disjoint consecutive pairs, at most one pair is lost
per exceptional site. -/
theorem private_pair_of_slack (P : Chain G n) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {s : ℕ} (hn : 4*s+3 ≤ n/2)
    (hd : n/2 ≤ G.degree (P.vertex 0)+s) (sat : ∀ z, ¬Good P z) :
    ∃ j k : Fin (n/2), 1 ≤ j.val ∧ k.val = j.val+1 ∧ PrivateContact P j ∧ PrivateContact P k := by
  classical
  obtain ⟨B,hB,good⟩ := private_contact_exceptions P c h4 (by omega) hd sat
  let lo (i : Fin (2*s+1)) : Fin (n/2) := ⟨2*i.val+1,by have := i.isLt; omega⟩
  let hi (i : Fin (2*s+1)) : Fin (n/2) := ⟨2*i.val+2,by have := i.isLt; omega⟩
  by_contra! h
  have hit (i : Fin (2*s+1)) : lo i ∈ B ∨ hi i ∈ B := by
    by_contra! miss
    exact h (lo i) (hi i) (by dsimp [lo]; omega) rfl (good _ miss.1) (good _ miss.2)
  let f (i : Fin (2*s+1)) : B := if hl : lo i ∈ B then ⟨lo i,hl⟩ else ⟨hi i,(hit i).resolve_left hl⟩
  have inj : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    have eq := congrArg (fun x : B => x.val.val) heq
    dsimp [f,lo,hi] at eq
    split_ifs at eq <;> dsimp at eq <;> omega
  have hh := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe,Fintype.card_fin] at hh
  omega

end Wall133
