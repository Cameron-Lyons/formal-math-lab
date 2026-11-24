import Wall133.SixProfiles
import Wall133.SixRowStalls
import Wall133.ShortChord

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem same_truth {a b c : Prop} (h : ¬ (a ↔ b)) (j : ¬ (a ↔ c)) : b ↔ c := by
  tauto

/-- Three initial choices force two stalled branches or two branches with a
second extension. Both cases yield an induced path on eighteen vertices. -/
theorem six_two_rows_force_path (P : Chain G 14) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hmin : ∀ u, 6 ≤ G.degree u) (hv : 10 ≤ G.degree (P.vertex 0)) : 18 ≤ G.path := by
  classical
  let A := (G.neighborFinset (P.vertex 0)).filter (Good P)
  have hc := good_card P c h4 (by decide)
  change G.degree (P.vertex 0) ≤ A.card+7 at hc
  obtain ⟨x,y,w,hx,hy,hw,hxy,hxw,hyw⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < A.card)
  have good {u : V} (hu : u ∈ A) := (Finset.mem_filter.mp hu).2
  let deep (u : V) := ∃ (hu : Good P u) (z : V), Good (grow P u hu) z
  have eqDeep {u w : V} (hu : Good P u) (hw : Good P w) (huw : u ≠ w)
      (he : deep u ↔ deep w) : 18 ≤ G.path := by
    by_cases hd : deep u
    · obtain ⟨_,z',hz'⟩ := he.mp hd
      obtain ⟨_,z,hz⟩ := hd
      by_contra short
      obtain ⟨S⟩ := six_profile_of_short P c h4 hu hw huw hz (hmin _) short
      obtain ⟨T⟩ := six_profile_of_short P c h4 hw hu huw.symm hz' (hmin _) short
      obtain ⟨t,v,a,b,g,ht,hu,hv',ha,hb,hg,hva,hvb,hvg⟩ :=
        six_profile_short_chord h4 hu hw huw hz hz' S T
      obtain ⟨Q,hQ⟩ := short_chord_detour P c ht hu hv' ha hb hg hva hvb hvg
      obtain ⟨W,_⟩ := Q.extend c h4 (by rw [hQ]; omega) (by rw [hQ]; omega)
      exact short W.length_le
    · let rows : Fin 2 ↪ V := ⟨![u,w],by
        intro i j e
        fin_cases i <;> fin_cases j <;> simp_all⟩
      have rowsGood (r : Fin 2) : Good P (rows r) := by fin_cases r <;> assumption
      apply two_even_row_stalls (d := 6) P c h4 (by decide) rows rowsGood (fun _ => hmin _)
      intro r z hz
      fin_cases r
      · exact hd ⟨hu,z,hz⟩
      · exact hd (he.mpr ⟨hw,z,hz⟩)
  by_cases e : deep x ↔ deep y
  · exact eqDeep (good hx) (good hy) hxy e
  by_cases f : deep x ↔ deep w
  · exact eqDeep (good hx) (good hw) hxw f
  exact eqDeep (good hy) (good hw) hyw (same_truth e f)

/-- Average neighborhood independence at least eleven forces an induced path
on eighteen vertices in every four-cycle-free bipartite graph. -/
theorem eighteen_le_path_of_eleven_le_l [Nonempty V] (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (hav : (11 : ℝ) ≤ l G) : 18 ≤ G.path := by
  classical
  let m : ℕ := 5
  obtain ⟨c⟩ := hb
  obtain ⟨a,S,hS,hmin,hsum⟩ :=
    exists_odd_degree_core_with_density c (by decide : 0 < m) (sum_degree_ge_of_le_l hav)
  have : Nonempty S := hS.to_subtype
  let H := G.induce (S : Set V)
  let C : H.Coloring (Fin 2) := ⟨fun x => c x.val, fun h => c.map_rel h⟩
  have h4' : NoFourCycle H := by
    intro x y a b hxy hxa hya hxb hyb
    exact Subtype.ext (h4 (x := x.val) (y := y.val) (fun h => hxy (Subtype.ext h))
      hxa hya hxb hyb)
  have hbase (x : S) : m+1 ≤ H.degree x := (Nat.le_add_right _ _).trans (hmin x)
  have hside (x : S) (he : C x = a) : m+1+1 ≤ H.degree x := by
    change c x.val = a at he
    simpa [he] using hmin x
  have sumle := Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun v _ => Nat.le_add_right m (if c v.val = a then 1 else 0))
  have hs : (m+1+4)*Fintype.card S ≤ ∑ v : S, H.degree v := calc
    _ ≤ (2*m)*Fintype.card S := Nat.mul_le_mul_right _ (by decide)
    _ = 2 * ∑ _v : S, m := by simp [Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ _ := (Nat.mul_le_mul_left 2 sumle).trans hsum
  obtain ⟨T,h₀,h₄⟩ := exists_high_four_chain_of_average C h4' (by decide) hs
  dsimp [m] at h₀ h₄ hbase hside
  obtain ⟨R,hR⟩ := rooted_chain_from_four T C h4' (by decide) hbase a hside (by omega)
  have hroot : R.reverse.vertex 0 = T.vertex 4 := by simpa [Chain.reverse] using hR
  have hp := six_two_rows_force_path R.reverse C h4' hbase (hroot ▸ h₄)
  have transfer := G.path_induce_le (S : Set V)
  change H.path ≤ _ at transfer
  omega

end Wall133
