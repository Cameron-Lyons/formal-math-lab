import Wall133.RootedFour
import Wall133.TwoSlack
import Wall133.HighFour

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem deep_two_slack {d : ℕ} (P : Chain G (2*d+2)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 7 ≤ d) {x y z : V} (hx : Good P x) (hy : Good P y)
    (hxy : x ≠ y) (hz : Good (grow P x hx) z) (hdz : d ≤ G.degree z) :
    2*d+6 ≤ G.path := by
  classical
  let Q := grow (grow P x hx) z hz
  by_contra hshort
  have sat (w : V) : ¬Good Q w := fun hw => hshort (grow Q w hw).length_le
  obtain ⟨B,hB,good⟩ := private_contact_exceptions Q c h4 (by omega) (s := 2)
    (by change (2*d+2+1+1)/2 ≤ G.degree z+2; omega) sat
  let m := (2*d+2+1+1)/2
  have right : 2*(m-1) = 2*d+2 := by dsimp [m]; omega
  have exceptional (i : Fin m) (hi : i.val = 1 ∨ i.val = m-1) : i ∈ B := by
    by_contra hh
    obtain ⟨b,hzb,hb⟩ := contactOnSuffix P Q (r := 2) (j := 2*i.val)
      (by omega) (by dsimp [m] at hi; omega) (by have := i.isLt; dsimp [m] at *; omega)
      (by omega) (fun _ _ => rfl)
      (fun j hj h => False.elim (hz.2.2 (j+1) (by omega) (by omega) h))
      i rfl (good i hh)
    exact hshort (path_of_private_end P c h4 (by omega) hx hy hxy hz hzb (2*i.val)
      (by rcases hi with h|h <;> omega) hb.fresh hb.contact)
  let first : Fin m := ⟨1,by dsimp [m]; omega⟩
  let last : Fin m := ⟨m-1,by dsimp [m]; omega⟩
  have e₁ := exceptional first (Or.inl rfl)
  have e₂ := exceptional last (Or.inr rfl)
  have hne : first ≠ last := fun he => by have := congrArg Fin.val he; dsimp [first,last,m] at this; omega
  let U := (B.erase first).erase last
  have hU : U.card ≤ 2 := by
    have hm : last ∈ B.erase first := Finset.mem_erase.mpr ⟨hne.symm,e₂⟩
    dsimp [U]
    rw [Finset.card_erase_of_mem hm,Finset.card_erase_of_mem e₁]
    omega
  let low (i : Fin 3) : Fin m := ⟨2*i.val+2,by have := i.isLt; dsimp [m]; omega⟩
  let high (i : Fin 3) : Fin m := ⟨2*i.val+3,by have := i.isLt; dsimp [m]; omega⟩
  have memU {j : Fin m} (hj : j ∈ B) (hlo : 2 ≤ j.val) (hhi : j.val ≤ 7) : j ∈ U := by
    apply Finset.mem_erase.mpr
    refine ⟨fun e => ?_,Finset.mem_erase.mpr ⟨fun e => ?_,hj⟩⟩
    · have := congrArg Fin.val e; dsimp [last,m] at this; omega
    · have := congrArg Fin.val e; dsimp [first] at this; omega
  have hit (i : Fin 3) : low i ∈ U ∨ high i ∈ U := by
    by_contra! miss
    have ii := i.isLt
    have p := good (low i) (fun e => miss.1 (memU e (by dsimp [low]; omega) (by dsimp [low]; omega)))
    have q := good (high i) (fun e => miss.2 (memU e (by dsimp [high]; omega) (by dsimp [high]; omega)))
    exact hshort (path_of_two_step_pair P c h4 hx hy hxy hz (low i) (high i) (by dsimp [low]; omega) rfl p q)
  let f (i : Fin 3) : U := if hl : low i ∈ U then ⟨low i,hl⟩ else ⟨high i,(hit i).resolve_left hl⟩
  have inj : Function.Injective f := by
    intro i j he
    apply Fin.ext
    have eq := congrArg (fun x : U => x.val.val) he
    dsimp [f,low,high] at eq
    split_ifs at eq <;> dsimp at eq <;> omega
  have hbound := Fintype.card_le_of_injective f inj
  simp only [Fintype.card_coe,Fintype.card_fin] at hbound
  omega

/-- A rooted even chain two edges longer than the minimum-degree guarantee
admits three further edges at a high root for minimum degree at least seven. -/
theorem longer_even_chain_detours {d : ℕ} (P : Chain G (2*d+2)) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hd : 7 ≤ d) (hmin : ∀ u, d ≤ G.degree u)
    (hv : d+3 ≤ G.degree (P.vertex 0)) : 2*d+6 ≤ G.path := by
  obtain ⟨x,y,hx,hy,hxy⟩ := two_good P c h4 (by omega) (by omega)
  by_cases sx : ∃ z, Good (grow P x hx) z
  · obtain ⟨z,hz⟩ := sx; exact deep_two_slack P c h4 hd hx hy hxy hz (hmin z)
  by_cases sy : ∃ z, Good (grow P y hy) z
  · obtain ⟨z,hz⟩ := sy; exact deep_two_slack P c h4 hd hy hx hxy.symm hz (hmin z)
  exact looseDoubleStalls P c h4 (by omega) hx hy hxy
    (by have := hmin x; omega) (by have := hmin y; omega)
    (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)

/-- Odd density thresholds at least thirteen force seven additional vertices
on an induced path in a four-cycle-free bipartite graph. -/
theorem add_seven_le_path_of_odd_bipartite_density [Nonempty V]
    (hb : G.IsBipartite) (h4 : NoFourCycle G) {m : ℕ} (hm : 6 ≤ m)
    (hav : (2*m+1 : ℕ) ≤ l G) : 2*m+1+7 ≤ G.path := by
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
  have hbase (x : S) : m+1 ≤ H.degree x := (Nat.le_add_right _ _).trans (hmin x)
  have hside (x : S) (he : C x = a) : m+1+1 ≤ H.degree x := by
    change c x.val = a at he
    simpa [he] using hmin x
  have sumle := Finset.sum_le_sum (s := (Finset.univ : Finset S))
    (fun v _ => Nat.le_add_right m (if c v.val = a then 1 else 0))
  have hs : (m+1+3)*Fintype.card S ≤ ∑ v : S, H.degree v := calc
    _ ≤ (2*m)*Fintype.card S := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * ∑ _v : S, m := by simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    _ ≤ _ := (Nat.mul_le_mul_left 2 sumle).trans hsum
  obtain ⟨T,h₀,h₄⟩ := exists_high_four_chain_of_average C h4' (by omega) hs
  obtain ⟨R,hR⟩ := rooted_chain_from_four T C h4' (by omega) hbase a hside (by omega)
  have hroot : R.reverse.vertex 0 = T.vertex 4 := by simpa [Chain.reverse] using hR
  have hp := longer_even_chain_detours R.reverse C h4' (by omega) hbase (hroot ▸ h₄)
  have transfer := G.path_induce_le (S : Set V)
  change H.path ≤ _ at transfer
  omega

end Wall133
