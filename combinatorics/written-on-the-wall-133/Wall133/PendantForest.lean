module

public import Wall133.CoreReturn
public import Wall133.BipartiteRadiusSix

@[expose] public section

/-! # Low degrees on a forest attached at a single vertex -/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private theorem hits_boundary (T : Finset V) (e : V)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    {z x : V} (p : G.Walk z x) (hz : z ∈ T) (hx : x ∉ T) : e ∈ p.support := by
  induction p with
  | nil => exact (hx hz).elim
  | @cons z w x h q ih =>
    rcases hsep z hz w h with hw | rfl
    · exact List.mem_cons_of_mem _ (ih hw hx)
    · exact List.mem_cons_of_mem _ q.start_mem_support

theorem dist_add_of_boundary (hc : G.Connected) (T : Finset V) (e : V)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    {x z : V} (hx : x ∉ T) (hz : z ∈ T) :
    G.dist x z = G.dist x e + G.dist e z := by
  classical
  obtain ⟨p,_,hp⟩ := hc.exists_path_of_dist z x
  have hmem := hits_boundary T e hsep p hz hx
  have hlen := congrArg Walk.length (p.take_spec hmem)
  simp only [Walk.length_append] at hlen
  have h₁ := dist_le (p.takeUntil e hmem)
  have h₂ := dist_le (p.dropUntil e hmem)
  have ht := hc.dist_triangle (u := x) (v := e) (w := z)
  rw [G.dist_comm (u := z) (v := e)] at h₁
  rw [G.dist_comm (u := e) (v := x)] at h₂
  rw [G.dist_comm (u := z) (v := x)] at hp
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- A subgraph of minimum degree three cannot enter an acyclic region that
is joined to its complement at just one vertex. -/
theorem core_disjoint_of_pendant_forest (T S : Finset V) (e : V)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    (hforest : (G.induce (T : Set V)).IsAcyclic)
    (hd : ∀ z : S, 3 ≤ (G.induce (S : Set V)).degree z) : Disjoint S T := by
  classical
  by_contra hn
  obtain ⟨x,hxS,hxT⟩ := Finset.not_disjoint_iff.mp hn
  let I := S ∩ T
  let H := G.induce (S : Set V)
  let K := G.induce (I : Set V)
  let : Nonempty I := ⟨⟨x,Finset.mem_inter.mpr ⟨hxS,hxT⟩⟩⟩
  let f : K →g G.induce (T : Set V) :=
    ⟨fun u => ⟨u.val,(Finset.mem_inter.mp u.property).2⟩,fun h => h⟩
  have hforest' : K.IsAcyclic := hforest.comap f (fun _ _ h => Subtype.ext (congrArg (fun w : T => w.val) h))
  obtain ⟨u,v,p,hp,hmax⟩ := Walk.exists_isPath_forall_isPath_length_le_length K
  let u' : S := ⟨u.val,(Finset.mem_inter.mp u.property).1⟩
  let N := (H.neighborFinset u').map (Function.Embedding.subtype (· ∈ S))
  have sub : N ⊆ {e,p.snd.val} := by
    intro w hw
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hw
    have hu : G.Adj u.val y.val := (H.mem_neighborFinset _ _).mp hy
    rcases hsep _ (Finset.mem_inter.mp u.property).2 _ hu with hT | he
    · let y' : I := ⟨y.val,Finset.mem_inter.mpr ⟨y.property,hT⟩⟩
      have haj : K.Adj u y' := hu
      have hmem : y' ∈ p.support := by
        by_contra hnew
        have hext := hmax _ _ (p.cons haj.symm) (hp.cons hnew)
        simp at hext
      have eq := congrArg Subtype.val (hforest'.eq_snd_of_adj_start hp haj hmem)
      exact Finset.mem_insert.mpr (.inr (Finset.mem_singleton.mpr eq))
    · exact Finset.mem_insert.mpr (.inl he)
  have hh := Finset.card_le_card sub
  have hcard : N.card = H.degree u' := by simp [N]
  have ht : ({e,p.snd.val} : Finset V).card ≤ 2 := Finset.card_insert_le _ _
      |>.trans_eq (by simp)
  have hdeg := hd u'
  change 3 ≤ H.degree u' at hdeg
  omega

private def outsideChoices (T : Finset V) (e : V)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    (hdeg : ∀ x ∉ T, x ≠ e → 3 ≤ G.degree x) {v : V} (hv : v ∉ T) (hne : v ≠ e) :
    ExteriorChoices G v 2 where
  allowed j := {x | (x ∉ T ∧ x ≠ e) ∨ j = 2}
  start := Or.inl ⟨hv,hne⟩
  choices j hj x hx _ := by
    change (x ∉ T ∧ x ≠ e) ∨ j = 2 at hx
    obtain ⟨hT,he⟩ := hx.resolve_right (by omega)
    have hd := hdeg x hT he
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · refine ⟨(G.neighborFinset x).erase e, ?_, ?_⟩
      · have hh := Finset.pred_card_le_card_erase (s := G.neighborFinset x) (a := e)
        rw [G.card_neighborFinset_eq_degree] at hh
        omega
      · intro y hy
        obtain ⟨hye,hn⟩ := Finset.mem_erase.mp hy
        have ha := (G.mem_neighborFinset _ _).mp hn
        exact ⟨ha, Or.inl ⟨fun hyT => (hsep y hyT x ha.symm).elim hT he,hye⟩⟩
    · exact ⟨G.neighborFinset x, hd, fun z hz => ⟨(G.mem_neighborFinset _ _).mp hz, Or.inr rfl⟩⟩

/-- WOWII 133 when all vertices of degree below three lie in an acyclic
region attached through a single boundary vertex. The boundary vertex
itself may have any degree. The region can have arbitrarily many leaves. -/
theorem radius_add_floor_le_path_of_pendant_forest [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (T : Finset V) (e : V) (hforest : (G.induce (T : Set V)).IsAcyclic)
    (hsep : ∀ z ∈ T, ∀ w, G.Adj z w → w ∈ T ∨ w = e)
    (hdegree : ∀ x ∉ T, x ≠ e → 3 ≤ G.degree x)
    (hr : 5+3*(⌊l G⌋₊%2) ≤ G.radius.toNat) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  by_cases hsmall : G.radius.toNat ≤ 6
  · exact radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hsmall
  by_contra! hbad
  let k := ⌊l G⌋₊
  change G.path < G.radius.toNat+k at hbad
  change 5+3*(k%2) ≤ G.radius.toNat at hr
  have hk : G.radius.toNat ≤ k := by have := chung_bound_nat G hc; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨c⟩ := hb
  obtain ⟨S,a,hd,hcost⟩ := exists_growth_anchor c (by omega : 7 ≤ k) (sum_degree_ge_of_le_l hav)
  have disj := core_disjoint_of_pendant_forest T S e hsep hforest
    (fun u => (by omega : 3 ≤ k/2+1).trans (hd u))
  obtain ⟨z,hz,hmax⟩ := (insert e T).exists_max_image (G.dist e) (Finset.insert_nonempty _ _)
  obtain ⟨a',hcol,hclose⟩ := exists_nearby_anchor hc c h4 S a z (by omega) hbad hd
  have hout := Finset.disjoint_left.mp disj a'.property
  have metric (w : V) (hw : w ∈ insert e T) :
      G.dist a'.val w = G.dist a'.val e + G.dist e w := by
    rcases Finset.mem_insert.mp hw with rfl | h
    · simp
    · exact dist_add_of_boundary hc T e hsep hout h
  have hzD := metric z hz
  obtain ⟨v,p,hp,hrad⟩ := exists_geodesic_ge_radius G hc a'.val
  have hfar : G.radius.toNat ≤ G.dist a'.val v := by omega
  have hv : v ∉ insert e T := by
    intro h
    have := hmax v h
    have := metric v h
    omega
  have hne : v ≠ e := fun he => hv (he ▸ Finset.mem_insert_self e T)
  have hvT : v ∉ T := fun he => hv (Finset.mem_insert_of_mem he)
  exact hbad.not_ge (radius_add_threshold_le_path_of_exterior_anchor hc c h4 (by omega : 7 ≤ k)
    S a' hd (by simpa only [hcol] using hcost) hfar (outsideChoices T e hsep hdegree hvT hne)
    (by omega))

end Wall133
