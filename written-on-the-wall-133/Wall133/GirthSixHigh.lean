import Wall133.GirthSixRotation

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V}

/-- Reverse the prefix up to the old antepenultimate vertex by starting
at the old far endpoint and crossing its private common neighbor. -/
private theorem rotated_ends (p : G.Walk u v) (hp : Chordless p) (hn : 4 ≤ p.length)
    {w : V} (huw : G.Adj u w) (hvw : G.Adj v w)
    (honly : ∀ i ≤ p.length, i ≠ 0 → G.Adj (p.getVert i) w → i=p.length) :
    ∃ q : G.Walk v (p.getVert (p.length-2)), q.length=p.length ∧ Chordless q := by
  let T := p.take (p.length-2)
  have hlen : T.length=p.length-2 := by simp [T]
  have idx (i) (hi : i ≤ T.length) : T.getVert i=p.getVert i := by
    simp [T,Nat.min_eq_right (show i ≤ p.length-2 by omega)]
  have ht : Chordless T := by
    refine ⟨hp.simple.take _,fun i j hi hj ha => ?_⟩
    rw [idx _ hi,idx _ hj] at ha
    exact hp.consecutive _ _ (by omega) (by omega) ha
  have far (i) (hi : i ≤ T.length) : ¬G.Adj v (T.getVert i) := by
    intro hadj
    rw [idx _ hi] at hadj
    have ha : G.Adj (p.getVert p.length) (p.getVert i) := by simpa only [Walk.getVert_length] using hadj
    have := hp.consecutive p.length i le_rfl (by omega) ha
    omega
  have hw : w ∉ T.support := ht.pending_off_path huw
    (fun he => far 1 (by omega) (he ▸ hvw))
  have clean (i) (hi : i ≤ T.length) (hpos : i ≠ 0) (hadj : G.Adj w (T.getVert i)) : False := by
    rw [idx _ hi] at hadj
    have := honly i (by omega) hpos hadj.symm
    omega
  let U := T.cons huw.symm
  have hU : Chordless U := ht.extend huw hw clean
  have hvT : v ∉ T.support := by
    intro h
    obtain ⟨i,he,hi⟩ := Walk.mem_support_iff_exists_getVert.mp h
    rw [idx i hi] at he
    rw [hlen] at hi
    have hfinal := hp.simple.getVert_injOn (x₁ := i) (x₂ := p.length)
      (show i ≤ p.length from hi.trans (Nat.sub_le _ _)) (Nat.le_refl p.length) (he.trans p.getVert_length.symm)
    omega
  have hvU : v ∉ U.support := by simp [U,hvw.ne,hvT]
  refine ⟨U.cons hvw,by simp [U,hlen]; omega,hU.extend hvw.symm hvU ?_⟩
  rintro (_|i) hi hpos hadj
  · contradiction
  · exact far i (by change i+1 ≤ T.length+1 at hi; omega) hadj

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem grow_at_high_degree (hg : 6 ≤ G.egirth) (p : G.Walk u v) (hp : Chordless p)
    (h : (p.length-2)/2 < G.degree u-1) :
    ∃ w, ∃ ha : G.Adj w u, Chordless (p.cons ha) := by
  by_contra! hno
  apply h.not_ge (saturated_degree_six hg hp ?_)
  intro w ha hoff
  by_contra! hclean
  exact hno w ha.symm (hp.extend ha hoff hclean)

omit [DecidableRel G.Adj] in
private theorem chordless_length (p : G.Walk u v) (hp : Chordless p) : p.length+1 ≤ G.path := by
  simpa only [Walk.length_support] using G.length_le_path_of_isInducedPath _
    (isInducedPath_support_of_isPath_of_adj_getVert p hp.simple hp.consecutive)

/-- If no induced path has more than 2d+2 vertices, vertices of degree
greater than d have pairwise disjoint neighborhoods at girth at least six. -/
theorem girth_six_high_no_common (hg : 6 ≤ G.egirth) {d : ℕ} (hd : 3 ≤ d)
    (hmin : ∀ u, d ≤ G.degree u) (hshort : G.path ≤ 2*d+2) {a b x : V}
    (ha : d < G.degree a) (hb : d < G.degree b) (hxa : G.Adj x a) (hxb : G.Adj x b) :
    a=b := by
  classical
  by_contra hne
  let T := hxa.toWalk
  have hTlen : T.length=1 := rfl
  have hgeo : T.length=G.dist x a := hTlen.trans (dist_eq_one_iff_adj.mpr hxa).symm
  have hT : Chordless T := ⟨T.isPath_of_length_eq_dist hgeo,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist T hgeo hi hj).1⟩
  have hoff : b ∉ T.support := by simp [T,Adj.toWalk,hxb.ne.symm,Ne.symm hne]
  let seed := T.cons hxb.symm
  have hseed : Chordless seed := hT.extend hxb hoff (fun i hi hpos hadj => by
    have h := first_blocker (g := 6) hg hT hxb hoff hi hpos hadj
    omega)
  obtain ⟨u,p,t,_,hp,hlen,hsuf,sat⟩ := exists_saturated Set.univ seed hseed (Set.mem_univ _)
  have blocked (w) := sat w (Set.mem_univ _)
  have hdeg := saturated_degree_six hg hp blocked
  have mind := hmin u
  have hpath := chordless_length p hp
  have plen : p.length=2*d := by
    by_contra h
    have he : p.length=2*d+1 := by omega
    obtain ⟨w,hw,hQ⟩ := grow_at_high_degree hg p.reverse hp.reverse (by simp only [Walk.length_reverse]; omega)
    have := chordless_length _ hQ
    simp only [Walk.length_cons,Walk.length_reverse] at this
    omega
  obtain ⟨w,huw,hend,honly⟩ := girth_six_private_end hg hp hd plen mind blocked
  rw [←plen,p.getVert_length] at hend
  rw [←plen] at honly
  obtain ⟨q,hq,hqpath⟩ := rotated_ends p hp (by omega) huw hend honly
  have final : p.getVert (p.length-2)=b := by
    have hs : seed.length=2 := rfl
    rw [hs] at hlen
    simpa [show p.length-2=t by omega,seed] using hsuf 0
  obtain ⟨z,hz,hR⟩ := grow_at_high_degree hg q hqpath (by omega)
  have bd : d < G.degree (p.getVert (p.length-2)) := final ▸ hb
  obtain ⟨z',hz',hR'⟩ := grow_at_high_degree hg (q.cons hz).reverse hR.reverse
    (by simp only [Walk.length_reverse,Walk.length_cons]; omega)
  have := chordless_length _ hR'
  simp only [Walk.length_cons,Walk.length_reverse] at this
  omega

end Wall133
