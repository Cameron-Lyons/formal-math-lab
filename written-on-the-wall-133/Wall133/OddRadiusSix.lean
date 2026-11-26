module

public import Wall133.OddFourSix
public import Wall133.OddSmallSix

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem sameTruth {s u w : Prop} (h₁ : ¬(s ↔ u)) (h₂ : ¬(s ↔ w)) : u ↔ w := by
  tauto

omit [Nonempty V] in
/-- Three clean neighbors of a root of degree at least 2d−1 suffice at every
asymmetric minimum degree d ≥ 4. -/
theorem odd_core_add_five_of_density_root (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (col : Fin 2)
    (hside : ∀ x, c x = col → d+1 ≤ G.degree x) (v : V)
    (hv : 2*d-1 ≤ G.degree v) : 2*d+5 ≤ G.path := by
  classical
  obtain ⟨R,hR⟩ := chain_odd_ending_at c h4 hd hmin col hside v
  let P := R.reverse
  have hP : P.vertex 0 = v := by simpa [P,Chain.reverse] using hR
  have hroot : 2*d-1 ≤ G.degree (P.vertex 0) := hP ▸ hv
  by_cases sat : ∀ x (hx : Good P x) z, ¬Good (grow P x hx) z
  · exact small_odd_double_stalls P c h4 hd hmin hroot sat
  push Not at sat
  obtain ⟨x,hx,z,hz⟩ := sat
  let A := (G.neighborFinset (P.vertex 0)).filter (Good P)
  have hcount := good_card P c h4 (by omega)
  change G.degree (P.vertex 0) ≤ A.card+(2*d+1)/2 at hcount
  obtain ⟨p,q,t,hp,hq,ht,hpq,hpt,hqt⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < A.card)
  have good {w : V} (hw : w ∈ A) := (Finset.mem_filter.mp hw).2
  have other : ∃ y, Good P y ∧ x ≠ y := by
    by_cases he : x=p
    · exact ⟨q,good hq,he ▸ hpq⟩
    · exact ⟨p,good hp,he⟩
  obtain ⟨y,hy,hxy⟩ := other
  by_cases hfive : 5 ≤ d
  · apply secondLevel P c h4 (by omega) hx hy hxy hz
    have := hmin z
    exact Or.inr ⟨Or.inl (by omega),by omega⟩
  have hd4 : d = 4 := by omega
  subst d
  by_cases hcol : c v = col
  · have e : c z = col := (color_common c (show G.Adj x z from hz.1).symm hx.1).trans
      ((congrArg c hP).trans hcol)
    exact secondLevel P c h4 (by decide) hx hy hxy hz (Or.inl (hside z e))
  have high {w : V} (hw : Good P w) : 5 ≤ G.degree w := by
    apply hside
    apply Fin.ext
    have diff := Fin.val_ne_of_ne (c.valid hw.1)
    rw [hP] at diff
    have := Fin.val_ne_of_ne hcol
    have := (c v).isLt; have := (c w).isLt; have := col.isLt
    omega
  let deep (w : V) := ∃ (hw : Good P w) (z : V), Good (grow P w hw) z
  have same {u w : V} (hu : Good P u) (hw : Good P w) (huw : u ≠ w)
      (he : deep u ↔ deep w) : 13 ≤ G.path := by
    by_cases de : deep u
    · obtain ⟨_,z',hz'⟩ := he.mp de
      obtain ⟨_,z'',hz''⟩ := de
      exact odd_four_two_deep_rows P c h4 hu hw huw hz'' hz' (hmin _) (hmin _)
    · obtain ⟨F,_⟩ := doubleStallsWithEnd P c h4 (by decide) hu hw huw (high hu) (high hw)
        (fun z hz => de ⟨hu,z,hz⟩) (fun z hz => de (he.mpr ⟨hw,z,hz⟩))
      exact F.length_le
  by_cases hp' : deep p ↔ deep q
  · exact same (good hp) (good hq) hpq hp'
  by_cases ht' : deep p ↔ deep t
  · exact same (good hp) (good ht) hpt ht'
  exact same (good hq) (good ht) hqt (sameTruth hp' ht')

/-- At odd average-degree thresholds at least seven, a four-cycle-free
bipartite graph contains an induced path of order at least the threshold plus six. -/
theorem add_six_le_path_of_odd_bipartite_density (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {m : ℕ} (hm : 3 ≤ m) (hav : (2*m+1 : ℕ) ≤ l G) : 2*m+1+6 ≤ path G := by
  classical
  obtain ⟨c⟩ := hb
  obtain ⟨a,S,hS,hmin,hsum⟩ :=
    exists_odd_degree_core_with_density c (by omega : 0 < m) (sum_degree_ge_of_le_l hav)
  have : Nonempty S := hS.to_subtype
  let H := G.induce (S : Set V)
  let C : H.Coloring (Fin 2) := ⟨fun x => c x.val, fun h => c.map_rel h⟩
  have h4' : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h))
      hxa hya hxb hyb)
  have hbase (x : S) : m+1 ≤ H.degree x :=
    (Nat.le_add_right _ _).trans (hmin x)
  have strong : ∃ v : S, c v.val = a := by
    obtain ⟨w,hw⟩ := hS
    let u : S := ⟨w,hw⟩
    by_cases hu : c u.val = a
    · exact ⟨u,hu⟩
    have hdeg := hbase u
    obtain ⟨z,hz⟩ := (H.degree_pos_iff_exists_adj u).mp (by omega)
    refine ⟨z,Fin.ext ?_⟩
    have diff := Fin.val_ne_of_ne (C.valid hz)
    change (c u.val).val ≠ (c z.val).val at diff
    have := Fin.val_ne_of_ne hu
    have := (c u.val).isLt; have := (c z.val).isLt; have := a.isLt
    omega
  have hhigh : ∃ v : S, 2*m+1 ≤ H.degree v := by
    by_contra! h
    obtain ⟨u,hu⟩ := strong
    have hle : ∑ v : S, H.degree v ≤ ∑ _v : S, 2*m :=
      Finset.sum_le_sum (fun v _ => by have := h v; omega)
    have hlt : ∑ _v : S, m < ∑ v : S, (m + if c v.val = a then 1 else 0) := by
      apply Finset.sum_lt_sum (fun v _ => Nat.le_add_right _ _)
      exact ⟨u,Finset.mem_univ _,by simp [hu]⟩
    have eq : (∑ _v : S, 2*m) = 2 * ∑ _v : S, m := by
      rw [Finset.mul_sum]
    rw [eq] at hle
    change 2 * _ ≤ ∑ v : S, H.degree v at hsum
    omega
  obtain ⟨v,hv⟩ := hhigh
  have hside (x : S) (he : C x = a) : m+1+1 ≤ H.degree x := by
    change c x.val = a at he
    simpa [he] using hmin x
  have hp := odd_core_add_five_of_density_root C h4' (by omega : 4 ≤ m+1) hbase a hside v (by omega)
  have htransfer := G.path_induce_le (S : Set V)
  change path H ≤ _ at htransfer
  omega

/-- The radius-six conjecture at odd neighborhood-independence floor at least seven. -/
theorem radius_add_floor_le_path_of_bipartite_radius_six_odd (hb : G.IsBipartite)
    (h4 : NoFourCycle G) (hr : G.radius.toNat ≤ 6) (hl : 7 ≤ ⌊l G⌋₊)
    (he : ⌊l G⌋₊ % 2 = 1) : G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  let k := ⌊l G⌋₊
  have eq : 2*(k/2)+1 = k := by dsimp [k]; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  have hp := add_six_le_path_of_odd_bipartite_density hb h4 (m := k/2)
    (by dsimp [k]; omega) (by rwa [eq])
  change _ + k ≤ _
  omega

end Wall133
