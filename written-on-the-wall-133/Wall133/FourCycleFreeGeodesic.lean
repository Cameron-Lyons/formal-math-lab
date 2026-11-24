import Wall133.CoreExterior

/-!
# Induced paths from both ends of a geodesic without a four-cycle

Each positive position on the path can block at most one neighbor of its
initial vertex. On a geodesic all blocking positions lie in an interval
of width four. If the far end has already been extended, only its last
few positions can be close enough to block growth at the other end.
-/
namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a b u v : V}

/-- This injection includes the first path neighbor by assigning it index two. -/
private theorem stalled_card {p : G.Walk u v} (hp : Chordless p) (h4 : NoFourCycle G)
    (hc : G.Connected) (hn : 2 ≤ p.length) (N : Finset V) (ha : ∀ w∈N, G.Adj u w)
    (sat : ∀ w∈N, w ∉ p.support → ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w (p.getVert i))
    {M : ℕ} (f : ℕ → ℕ)
    (bound : ∀ i ≤ p.length, i ≠ 0 → G.dist u (p.getVert i) ≤ 2 → f i < M)
    (inj : ∀ i j, i ≤ p.length → j ≤ p.length → i ≠ 0 → j ≠ 0 →
      G.dist u (p.getVert i) ≤ 2 → G.dist u (p.getVert j) ≤ 2 → f i=f j → i=j) :
    N.card ≤ M := by
  classical
  have block (w : N) : ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w.val (p.getVert i) := by
    by_cases h : w.val=p.getVert 1
    · exact ⟨2,hn,by decide,h ▸ p.adj_getVert_succ (i := 1) (by omega)⟩
    · exact sat w.val w.property (hp.pending_off_path (ha _ w.property) h)
  choose idx hi hpos hadj using block
  have near (w : N) : G.dist u (p.getVert (idx w)) ≤ 2 := by
    have := hc.dist_triangle (u := u) (v := w.val) (w := p.getVert (idx w))
    simpa only [dist_eq_one_iff_adj.mpr (ha _ w.property),dist_eq_one_iff_adj.mpr (hadj w)] using this
  let F (w : N) : Fin M := ⟨f (idx w),bound _ (hi w) (hpos w) (near w)⟩
  have hinj : Function.Injective F := by
    intro x y he
    have hxy := inj _ _ (hi x) (hi y) (hpos x) (hpos y) (near x) (near y) (congrArg Fin.val he)
    apply Subtype.ext
    apply h4 (x := u) (y := p.getVert (idx x)) _ (ha _ x.property) (hadj x).symm (ha _ y.property)
    · rw [hxy]; exact (hadj y).symm
    · intro eq
      have e := hp.simple.getVert_injOn (x₁ := 0) (x₂ := idx x) (Nat.zero_le _) (hi x)
        (by simpa only [Walk.getVert_zero] using eq)
      exact hpos x e.symm
  simpa using Fintype.card_le_of_injective F hinj

theorem stalled_geodesic_middle_bound {p : G.Walk u v} (hp : Chordless p) (h4 : NoFourCycle G)
    (hc : G.Connected) (q : G.Walk a b) (hq : q.length=G.dist a b)
    (hn : 2 ≤ p.length) {r s : ℕ} (hlen : p.length=r+q.length+s)
    (hm : ∀ j ≤ q.length, p.getVert (r+j)=q.getVert j) (N : Finset V)
    (ha : ∀ w∈N, G.Adj u w)
    (sat : ∀ w∈N, w ∉ p.support → ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    N.card ≤ min ((r-1)+5) (min (r+q.length) (2*r+2)) + min s (s+r+3-q.length) := by
  let P := chainOfChordless p hp
  have seg (i j : ℕ) (ij : i ≤ j) (hj : j ≤ p.length) :
      G.dist (p.getVert i) (p.getVert j) ≤ j-i := P.dist_le_sub hc ij hj
  have start : p.getVert r=a := by simpa using hm 0 (Nat.zero_le _)
  have last : p.getVert (r+q.length)=b := by simpa using hm q.length le_rfl
  have startDist : G.dist a u ≤ r := by
    have h := seg 0 r (Nat.zero_le _) (by omega)
    simpa only [Walk.getVert_zero,start,Nat.sub_zero,G.dist_comm (u := u) (v := a)] using h
  let lo := r+q.length-(G.dist u b+2)
  have window {i : ℕ} (hri : r ≤ i) (hiq : i ≤ r+q.length)
      (hnear : G.dist u (p.getVert i) ≤ 2) : lo ≤ i ∧ i ≤ lo+4 := by
    have hdist : G.dist (p.getVert i) b=q.length-(i-r) := by
      rw [← Nat.add_sub_of_le hri,hm (i-r) (by omega)]
      simpa only [Walk.getVert_length,Nat.add_sub_cancel_left] using
        dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := i-r) (j := q.length) (by omega) le_rfl
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert i) (w := b)
    have h₂ := hc.dist_triangle (u := p.getVert i) (v := u) (w := b)
    rw [G.dist_comm (u := p.getVert i) (v := u)] at h₂
    dsimp [lo]; omega
  let lower := max (r+q.length+1) (2*q.length-2)
  have tail {i : ℕ} (hi : i ≤ p.length) (ht : r+q.length < i)
      (hnear : G.dist u (p.getVert i) ≤ 2) : lower ≤ i := by
    have hs := seg (r+q.length) i (by omega) hi
    rw [last,G.dist_comm (u := b) (v := p.getVert i)] at hs
    have h₁ := hc.dist_triangle (u := a) (v := u) (w := p.getVert i)
    have h₂ := hc.dist_triangle (u := a) (v := p.getVert i) (w := b)
    dsimp [lower]; omega
  have long : N.card ≤ (r-1)+5+min s (s+r+3-q.length) := by
    let code i := if i<r then i-1 else if i≤r+q.length then (r-1)+(i-lo)
      else (r-1)+5+(i-lower)
    apply stalled_card hp h4 hc hn N ha sat code
    · intro i hi hpos hnear
      dsimp [code]
      split_ifs with h h'
      · omega
      · have := window (by omega) h' hnear; omega
      · have := tail hi (by omega) hnear
        dsimp [lower] at *
        omega
    · intro i j hi hj hpi hpj hni hnj he
      have wi := @window i; have wj := @window j
      have ti := @tail i hi; have tj := @tail j hj
      dsimp [code] at he
      split_ifs at he <;> omega
  let m := min (r+q.length) (2*r+2)
  have boundStart {i : ℕ} (hi : i ≤ r+q.length) (near : G.dist u (p.getVert i) ≤ 2) : i ≤ m := by
    dsimp [m]
    by_cases hr : i < r
    · omega
    have e : p.getVert i=q.getVert (i-r) := by simpa only [Nat.add_sub_of_le (by omega : r ≤ i)] using hm (i-r) (by omega)
    have hd : G.dist a (p.getVert i)=i-r := by
      rw [e]
      simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := 0) (j := i-r)
        (Nat.zero_le _) (by omega)
    have := hc.dist_triangle (u := a) (v := u) (w := p.getVert i)
    omega
  have short : N.card ≤ m+min s (s+r+3-q.length) := by
    let code i := if i≤r+q.length then i-1 else m+(i-lower)
    apply stalled_card hp h4 hc hn N ha sat code
    · intro i hi hpos hnear
      dsimp only [code]
      split_ifs with he
      · have := boundStart he hnear; omega
      · have := tail hi (by omega) hnear
        dsimp [lower] at *
        omega
    · intro i j hi hj hpi hpj hni hnj he
      have w₁ := @boundStart i; have w₂ := @boundStart j
      have t₁ := @tail i hi; have t₂ := @tail j hj
      dsimp only [code] at he
      split_ifs at he <;> omega
  change N.card ≤ min ((r-1)+5) m + _
  omega

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Grow twice from an arbitrary geodesic. A long geodesic yields its
length plus the minimum degree as a lower bound on the path number. -/
theorem geodesic_degree_bounds_of_noFourCycle (hc : G.Connected) (h4 : NoFourCycle G)
    (q : G.Walk a b) (hq : q.length=G.dist a b) (hD : 2 ≤ q.length)
    {d : ℕ} (hmin : ∀ x, d ≤ G.degree x) :
    q.length+d ≤ G.path+2 ∧ (q.length ≠ 4 → q.length+d ≤ G.path+1) ∧
    (8 ≤ q.length → 7 ≤ d → q.length+d ≤ G.path) := by
  classical
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨x,p,t,_,hp,hlen,hsuf,sat⟩ := exists_saturated Set.univ q hq' (Set.mem_univ a)
  have grow₁ := stalled_geodesic_middle_bound hp h4 hc q hq (by omega)
    (s := 0) (by omega : p.length=t+q.length+0) (fun j _ => hsuf j)
    (G.neighborFinset x) (fun w hw => (G.mem_neighborFinset _ _).mp hw)
    (fun w hw => sat w (Set.mem_univ _) ((G.mem_neighborFinset _ _).mp hw))
  rw [G.card_neighborFinset_eq_degree] at grow₁
  obtain ⟨y,P,j,_,hP,hL,hf,sat'⟩ := exists_saturated Set.univ p.reverse hp.reverse (Set.mem_univ b)
  have hrev : q.reverse.length=G.dist b a := by simpa [G.dist_comm] using hq
  have hL' : P.length=j+q.reverse.length+t := by simp only [Walk.length_reverse] at *; omega
  have middle (i : ℕ) (hi : i ≤ q.reverse.length) : P.getVert (j+i)=q.reverse.getVert i := by
    rw [hf,Walk.getVert_reverse,Walk.getVert_reverse,show p.length-i=t+(q.length-i) by
      simp only [Walk.length_reverse] at hi; omega,hsuf]
  have hPtwo : 2 ≤ P.length := by
    simp only [Walk.length_reverse] at hL
    omega
  have grow₂ := stalled_geodesic_middle_bound hP h4 hc q.reverse hrev hPtwo
    hL' middle (G.neighborFinset y) (fun w hw => (G.mem_neighborFinset _ _).mp hw)
    (fun w hw => sat' w (Set.mem_univ _) ((G.mem_neighborFinset _ _).mp hw))
  rw [G.card_neighborFinset_eq_degree,Walk.length_reverse] at grow₂
  have path := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert P
    hP.simple hP.consecutive)
  rw [Walk.length_support] at path
  simp only [Walk.length_reverse] at hL'
  have := hmin x; have := hmin y
  omega

end Wall133
