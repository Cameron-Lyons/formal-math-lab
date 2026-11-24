import Wall133.GirthSix

/-! # Extending geodesics at girth six

Contact indices before the original geodesic start at four and are separated
by at least two. On the geodesic they lie in an interval of width four.
-/

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem count_girth_six_contacts {W : Finset V} (idx : W → ℕ)
    (hlo : ∀ w, 4 ≤ idx w) (gap : ∀ w z, w ≠ z → idx w ≤ idx z → idx w+2 ≤ idx z)
    (t b : ℕ) (window : ∀ w, t ≤ idx w → b ≤ idx w ∧ idx w ≤ b+4) :
    W.card ≤ (t-3)/2+3 := by
  let code (w : W) := if idx w<t then (idx w-4)/2 else (t-3)/2+(idx w-b)/2
  let f (w : W) : Fin ((t-3)/2+3) := ⟨code w,by
    dsimp [code]
    split_ifs
    · have := hlo w; omega
    · have := window w (by omega); omega⟩
  have inj : Function.Injective f := by
    intro w z eq
    by_contra hne
    have hsep : idx w+2 ≤ idx z ∨ idx z+2 ≤ idx w := by
      rcases le_total (idx w) (idx z) with h|h
      · exact Or.inl (gap w z hne h)
      · exact Or.inr (gap z w (Ne.symm hne) h)
    have he := congrArg Fin.val eq
    change code w=code z at he
    have := hlo w; have := hlo z
    dsimp [code] at he
    split_ifs at he <;> first | omega | (have := window w (by omega); have := window z (by omega); omega)
  simpa using Fintype.card_le_of_injective f inj

/-- A core of minimum internal degree d ≥ 5 extends an eccentric geodesic
to an induced path on at least radius plus 2d minus four vertices. -/
theorem girth_six_radius_core_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hg : 6 ≤ G.egirth) (hc : G.Connected) (S : Finset V) (hS : S.Nonempty)
    {d : ℕ} (hd : 5 ≤ d) (hmin : ∀ x : S, d ≤ (G.induce (S : Set V)).degree x) :
    G.radius.toNat + 2*d ≤ G.path+4 := by
  classical
  obtain ⟨a,ha⟩ := hS
  obtain ⟨v,q,hq,hr⟩ := exists_geodesic_ge_radius G hc a
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,hu,hp,hlen,hsuf,hb⟩ := exists_saturated (S : Set V) q hq' ha
  let H := G.induce (S : Set V)
  let U : S := ⟨u,hu⟩
  let A := (H.neighborFinset U).map (Function.Embedding.subtype (· ∈ S))
  let W := A.erase (p.getVert 1)
  have info (w : W) : G.Adj u w.val ∧ w.val ∉ p.support ∧ w.val ∈ S := by
    obtain ⟨hne,hw⟩ := Finset.mem_erase.mp w.property
    obtain ⟨z,hz,he⟩ := Finset.mem_map.mp hw
    have adj : G.Adj u w.val := he ▸ (H.mem_neighborFinset _ _).mp hz
    exact ⟨adj,hp.pending_off_path adj hne,he ▸ z.property⟩
  choose idx hi hpos hadj using fun w : W => hb w.val (info w).2.2 (info w).1 (info w).2.1
  have hlo (w : W) : 4 ≤ idx w := by
    have := first_blocker (g := 6) hg hp (info w).1 (info w).2.1 (hi w) (hpos w) (hadj w)
    omega
  have gap (w z : W) (hne : w ≠ z) (hle : idx w ≤ idx z) : idx w+2 ≤ idx z := by
    have := separated_blockers (g := 6) hg hp (info w).1 (info z).1 (info w).2.1 (info z).2.1
      (fun he => hne (Subtype.ext he)) (by have := hlo w; omega) hle (hi z) (hadj w) (hadj z) (by decide)
    omega
  let b := p.length-(G.dist u v+2)
  have window (w : W) (hs : t ≤ idx w) : b ≤ idx w ∧ idx w ≤ b+4 := by
    let j := idx w-t
    have hj : j ≤ q.length := by have := hi w; dsimp [j]; omega
    have he : p.getVert (idx w) = q.getVert j := Nat.add_sub_of_le hs ▸ hsuf j
    have hdist : G.dist (p.getVert (idx w)) v = q.length-j := by
      rw [he]
      simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq hj le_rfl
    have hnear : G.dist u (p.getVert (idx w)) ≤ 2 :=
      (hc.dist_triangle (u := u) (v := w.val) (w := p.getVert (idx w))).trans_eq
        (by rw [dist_eq_one_iff_adj.mpr (info w).1,dist_eq_one_iff_adj.mpr (hadj w)])
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert (idx w)) (w := v)
    have h₂ := hc.dist_triangle (u := p.getVert (idx w)) (v := u) (w := v)
    rw [G.dist_comm (u := p.getVert (idx w)) (v := u)] at h₂
    dsimp [b,j] at *
    omega
  have count := count_girth_six_contacts idx hlo gap t b window
  have hsize : A.card = H.degree U := by simp [A]
  have hrem : A.card-1 ≤ W.card := Finset.pred_card_le_card_erase
  have hdeg : d ≤ H.degree U := hmin U
  have plen := G.length_le_path_of_isInducedPath _
    (isInducedPath_support_of_isPath_of_adj_getVert p hp.simple hp.consecutive)
  rw [Walk.length_support] at plen
  omega

/-- At girth six, an even average-degree threshold loses at most two
vertices from the proposed radius bound. An odd threshold loses at most three. -/
theorem radius_add_density_le_path_girth_six [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] (hg : 6 ≤ G.egirth) (hc : G.Connected) {k : ℕ}
    (hav : k*Fintype.card V ≤ ∑ v,G.degree v) : G.radius.toNat+k ≤ G.path+2+(k%2) := by
  by_cases hk : 8 ≤ k
  · obtain ⟨S,hS,hmin⟩ := exists_degree_core G (by omega) hav
    have := girth_six_radius_core_bound hg hc S hS (by omega : 5 ≤ k/2+1) hmin
    omega
  have hchung := chung_bound_nat G hc
  by_cases hsmall : k ≤ 3
  · have := radius_add_one_le_path G hc
    omega
  have hpath := girth_six_density_bound hg (by omega : 4 ≤ k) hav
  omega

/-- The floored inequality with a two-vertex error for even floors and a
three-vertex error for odd floors, at every radius. -/
theorem radius_add_floor_le_path_girth_six [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    [Nonempty V] (hg : 6 ≤ G.egirth) (hc : G.Connected) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path+2+(⌊l G⌋₊%2) := by
  apply radius_add_density_le_path_girth_six hg hc
  apply sum_degree_ge_of_le_l (G := G)
  exact Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v)))
    (Nat.cast_nonneg _))

end Wall133
