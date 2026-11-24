import Wall133.ShortGirthExact

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The neighborhood threshold is only needed near the two ends of the
selected geodesic. Internal geodesic vertices are unrestricted. -/
theorem geodesic_add_threshold_of_local_ends (h4 : NoFourCycle G) (hc : G.Connected)
    {d : ℕ} {a v : V} (q : G.Walk a v) (hq : q.length=G.dist a v) (hlen : 2 ≤ q.length)
    (hv : d≤G.indepNeighborsCard v)
    (start : min 2 d ≤ max (G.indepNeighborsCard a) (G.degree a-1))
    (source : ∀ u, u∉q.support → G.dist a u+3 < d →
      d≤G.indepNeighborsCard u ∨ d+1≤G.degree u)
    (finish : ∀ x y,G.Adj v x → G.Adj v y → x∉q.support → y∉q.support → x≠y → ¬G.Adj x y →
      (d≤G.indepNeighborsCard x ∨ d+1≤G.degree x) ∨
      (d≤G.indepNeighborsCard y ∨ d+1≤G.degree y)) :
    q.length+d≤G.path := by
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,_,hp,hl,hs,hb⟩ := exists_saturated Set.univ q hq' (Set.mem_univ _)
  let f (w : V) := max (G.indepNeighborsCard w) (G.degree w-1)
  have ctrl : GirthFiveSlotControl G f := by
    intro u v p hp hn k code bound inj sat
    obtain ⟨W,hW,⟨hα,hdeg⟩,idx,hI,hp'⟩ := exists_stalled_contacts_at hc h4 hp hn sat
    have pos (w : W) : GirthFivePossible p (idx w) := ⟨(hp' w).1,(hp' w).2.1,(hp' w).2.2.2⟩
    let rank (w : W) : Fin k := ⟨code (idx w),bound _ (pos w)⟩
    have fi : Function.Injective rank := fun w z e => hI (inj _ _ (pos w) (pos z) (congrArg Fin.val e))
    have cnt : W.card ≤ k := by simpa using Fintype.card_le_of_injective rank fi
    change max _ _ ≤ k+1
    exact max_le (by omega) (by omega)
  obtain ⟨count,zero⟩ := girth_five_first_growth q hq p hp hc ctrl
    (by omega) hl hs (le_refl (f u)) (fun w => hb w (Set.mem_univ _))
  have first : d ≤ t+3 := by
    by_contra! small
    have anchor : p.getVert t=a := by simpa using hs 0
    by_cases inside : u∈q.support
    · obtain ⟨i,eq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp inside
      have hidx := hp.simple.getVert_injOn (x₁ := 0) (x₂ := t+i) (Nat.zero_le p.length) (show t+i≤p.length by omega)
        (by rw [Walk.getVert_zero,hs,eq])
      have ht : t=0 := by omega
      have hu : u=a := by simpa [ht] using anchor
      have low := zero ht
      rw [hu] at low
      change f a ≥ min 2 d at start
      omega
    · have dist : G.dist a u ≤ t := by
        rw [G.dist_comm,←anchor]; exact (dist_le (p.take t)).trans (by simp)
      have w := source u inside (by omega)
      dsimp [f] at count
      omega
  let P := (chainOfChordless p hp).reverse
  have pref (i) (hi : i≤q.length) : P.vertex i=q.getVert (q.length-i) := by
    change p.getVert (p.length-i) = _
    rw [show p.length-i=t+(q.length-i) by omega,hs]
  have geo (i) (hi : i≤q.length) : G.dist (P.vertex 0) (P.vertex i)=i := by
    rw [pref 0 (by omega),pref i hi]
    simpa [G.dist_comm (u := v),show q.length-(q.length-i)=i by omega] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (show q.length-i≤q.length by omega) le_rfl
  apply two_at_geodesic_end P h4 hc hlen (by omega) geo (by omega) (by simpa [pref 0 (by omega)] using hv)
  intro ht x y hx hy hxy nxy
  have root : P.vertex 0=v := by simpa using pref 0 (by omega)
  have off {w} (h : Good P w) : w∉q.support := by
    intro hw
    obtain ⟨i,e,hi⟩ := Walk.mem_support_iff_exists_getVert.mp hw
    have eq := pref (q.length-i) (by omega)
    rw [show q.length-(q.length-i)=i by omega,e] at eq
    exact h.2.1 (q.length-i) (by omega) eq.symm
  rcases finish x y (root ▸ hx.1) (root ▸ hy.1) (off hx) (off hy) hxy nxy with wx|wy
  · exact extend_two_or_reroute_at P h4 hc hlen (by omega) geo ht hx hy hxy nxy wx
  · exact extend_two_or_reroute_at P h4 hc hlen (by omega) geo ht hy hx hxy.symm (fun h => nxy h.symm) wy

end Wall133
