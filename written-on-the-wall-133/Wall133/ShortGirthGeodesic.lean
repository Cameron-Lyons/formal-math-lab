import Wall133.ShortGirthDensity
import Wall133.IndependentContacts

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def GirthFivePossible {u v : V} (p : G.Walk u v) (i : ℕ) : Prop :=
  3 ≤ i ∧ i ≤ p.length ∧ G.dist u (p.getVert i) ≤ 2

private theorem count_slots {u v : V} (p : G.Walk u v) (hg : 5 ≤ G.egirth)
    (hc : G.Connected) (hp : Chordless p) {k : ℕ} (code : ℕ → ℕ)
    (bound : ∀ i, GirthFivePossible p i → code i < k)
    (inj : ∀ i j, GirthFivePossible p i → GirthFivePossible p j → code i=code j → i=j)
    (sat : ∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length, i≠0 ∧ G.Adj w (p.getVert i)) :
    G.degree u ≤ k+1 := by
  classical
  let W := (G.neighborFinset u).erase (p.getVert 1)
  have info (w : W) : G.Adj u w.val ∧ w.val ∉ p.support := by
    obtain ⟨hne,hadj⟩ := Finset.mem_erase.mp w.property
    have ha := (G.mem_neighborFinset _ _).mp hadj
    exact ⟨ha,hp.pending_off_path ha hne⟩
  choose idx hi hpos hadj using fun w : W => sat w.val (info w).1 (info w).2
  have pos (w : W) : GirthFivePossible p (idx w) := by
    have h := first_blocker (g := 5) hg hp (info w).1 (info w).2 (hi w) (hpos w) (hadj w)
    refine ⟨by omega,hi w,?_⟩
    exact (hc.dist_triangle (u := u) (v := w.val) (w := p.getVert (idx w))).trans_eq
      (by rw [dist_eq_one_iff_adj.mpr (info w).1,dist_eq_one_iff_adj.mpr (hadj w)])
  let f (w : W) : Fin k := ⟨code (idx w),bound _ (pos w)⟩
  have fi : Function.Injective f := by
    intro w z e
    by_contra ne
    have eq := inj _ _ (pos w) (pos z) (congrArg Fin.val e)
    have := separated_blockers (g := 5) hg hp (info w).1 (info z).1 (info w).2 (info z).2
      (fun e' => ne (Subtype.ext e')) (by have := hpos w; omega) (by omega) (hi z)
      (hadj w) (hadj z) (by decide)
    omega
  have lower : G.degree u-1 ≤ W.card := Finset.pred_card_le_card_erase
  have upper : W.card ≤ k := by simpa using Fintype.card_le_of_injective f fi
  omega

def GirthFiveSlotControl (G : SimpleGraph V) (weight : V → ℕ) : Prop :=
  ∀ {u v : V} (p : G.Walk u v), Chordless p → 2 ≤ p.length →
    ∀ {k : ℕ} (code : ℕ → ℕ), (∀ i, GirthFivePossible p i → code i < k) →
      (∀ i j, GirthFivePossible p i → GirthFivePossible p j → code i=code j → i=j) →
      (∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length, i≠0 ∧ G.Adj w (p.getVert i)) →
      weight u ≤ k+1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem girth_five_first_growth {a v u : V} (q : G.Walk a v) (hq : q.length=G.dist a v)
    (p : G.Walk u v) (hp : Chordless p) (hc : G.Connected)
    {weight : V → ℕ} (ctrl : GirthFiveSlotControl G weight) (hp2 : 2 ≤ p.length)
    {t d : ℕ} (hlen : p.length=t+q.length) (hs : ∀ j, p.getVert (t+j)=q.getVert j)
    (hd : d ≤ weight u)
    (sat : ∀ w, G.Adj u w → w ∉ p.support → ∃ i ≤ p.length, i≠0 ∧ G.Adj w (p.getVert i)) :
    d ≤ t+3 ∧ (t=0 → d≤1) := by
  let base := p.length-(G.dist u v+2)
  have anchor : p.getVert t=a := by simpa using hs 0
  have near : G.dist u a ≤ t := by
    rw [←anchor]; exact (dist_le (p.take t)).trans (by simp)
  have ring (i : ℕ) (hi : GirthFivePossible p i) (ht : t ≤ i) :
      base ≤ i ∧ i ≤ base+4 ∧ i ≤ 2*t+2 := by
    let j := i-t
    have hj : j ≤ q.length := by have := hi.2.1; dsimp [j]; omega
    have he : p.getVert i=q.getVert j := Nat.add_sub_of_le ht ▸ hs j
    have toEnd : G.dist (p.getVert i) v=q.length-j := by
      rw [he]; simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq hj le_rfl
    have fromStart : G.dist a (p.getVert i)=j := by
      rw [he]; simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le j) hj
    have := hc.dist_triangle (u := a) (v := u) (w := p.getVert i)
    have h₁ := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
    have h₂ := hc.dist_triangle (u := p.getVert i) (v := u) (w := v)
    rw [G.dist_comm (u := p.getVert i) (v := u)] at h₂
    rw [G.dist_comm (u := a) (v := u)] at this
    have := hi.2.2
    dsimp [base,j] at *
    omega
  have zero (e : t=0) : d≤1 := by
    have empty (i : ℕ) (hi : GirthFivePossible p i) : False := by
      have h := ring i hi (by omega); have := hi.1; omega
    have hh := ctrl p hp hp2 (k := 0) (fun _ => 0) (fun i hi => (empty i hi).elim)
      (fun i _ hi _ _ => (empty i hi).elim) sat
    omega
  refine ⟨?_,zero⟩
  by_cases ht : 3 ≤ t
  · let code (i : ℕ) := if i<t then i-3 else t-3+(i-base)
    have bound (i) (hi : GirthFivePossible p i) : code i<t+2 := by
      dsimp [code]; split_ifs with h
      · omega
      · have := ring i hi (by omega); omega
    have inj (i j) (hi : GirthFivePossible p i) (hj : GirthFivePossible p j) (he : code i=code j) : i=j := by
      have := hi.1; have := hj.1
      dsimp [code] at he
      split_ifs at he <;> first | omega | (have := ring i hi (by omega); have := ring j hj (by omega); omega)
    have := ctrl p hp hp2 code bound inj sat
    omega
  · have bound (i) (hi : GirthFivePossible p i) : i-3<t+2 := by
      have := hi.1
      have := ring i hi (by omega)
      omega
    have inj (i j) (hi : GirthFivePossible p i) (hj : GirthFivePossible p j) (he : i-3=j-3) : i=j := by
      have := hi.1; have := hj.1; omega
    have := ctrl p hp hp2 (·-3) bound inj sat
    omega

omit [DecidableRel G.Adj] in
/-- If the original geodesic has at least five edges, growth at its two ends
adds at least d−1 vertices in a graph of minimum degree d and girth five. -/
private theorem geodesic_growth (hc : G.Connected) {weight : V → ℕ} (ctrl : GirthFiveSlotControl G weight)
    {d : ℕ} (hmin : ∀ x, d ≤ weight x) {a v : V} (q : G.Walk a v)
    (hq : q.length=G.dist a v) (hfive : 5 ≤ q.length) : q.length+d ≤ G.path := by
  classical
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,_,hp,hl,hs,hb⟩ := exists_saturated Set.univ q hq' (Set.mem_univ _)
  obtain ⟨first,zero⟩ := girth_five_first_growth q hq p hp hc ctrl (by omega) hl hs (hmin _) (fun w => hb w (Set.mem_univ _))
  obtain ⟨x,r,s,_,hr,hlr,hsr,hbr⟩ := exists_saturated Set.univ p.reverse hp.reverse (Set.mem_univ _)
  have len : r.length=s+t+q.length := by simpa [hl,Nat.add_assoc] using hlr
  have vertices := G.length_le_path_of_isInducedPath _
    (isInducedPath_support_of_isPath_of_adj_getVert r hr.simple hr.consecutive)
  rw [Walk.length_support] at vertices
  by_contra! short
  have small : s ≤ 1 := by omega
  have lengthP := p.length_reverse
  have far : r.getVert s = v := by simpa using hsr 0
  have close : G.dist x v ≤ s := by
    rw [←far]; exact (dist_le (r.take s)).trans (by simp)
  have geo (i) (hi : GirthFivePossible r i) (he : i ≤ s+q.length) : i ≤ 2*s+2 := by
    let j := i-s
    have hj : j ≤ q.length := by dsimp [j]; omega
    have hs' : s ≤ i := by have := hi.1; omega
    have eq : r.getVert i=q.getVert (q.length-j) := by
      rw [←show s+j=i by dsimp [j]; omega,hsr,Walk.getVert_reverse,
        show p.length-j=t+(q.length-j) by omega,hs]
    have hd : G.dist (r.getVert i) v=j := by
      rw [eq]
      have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq
        (show q.length-j ≤ q.length by omega) le_rfl
      simpa [show q.length-(q.length-j)=j by omega] using hh
    have h := hc.dist_triangle (u := r.getVert i) (v := x) (w := v)
    rw [G.dist_comm (u := r.getVert i) (v := x)] at h
    have := hi.2.2; dsimp [j] at hd
    omega
  have forbid (i) (hi : GirthFivePossible r i) : i≠s+q.length+1 := by
    rintro rfl
    have hti : 1 ≤ t := by have := hi.2.1; omega
    have eq : r.getVert (s+q.length+1)=p.getVert (t-1) := by
      rw [Nat.add_assoc,hsr,Walk.getVert_reverse,show p.length-(q.length+1)=t-1 by omega]
    have adj : G.Adj (p.getVert (t-1)) a := by
      have ha : p.getVert t=a := by simpa using hs 0
      rw [←ha,←show t-1+1=t by omega]
      exact p.adj_getVert_succ (by omega)
    have h₁ := hc.dist_triangle (u := v) (v := x) (w := r.getVert (s+q.length+1))
    have h₂ := hc.dist_triangle (u := v) (v := r.getVert (s+q.length+1)) (w := a)
    rw [G.dist_comm (u := v) (v := x)] at h₁
    rw [G.dist_comm (u := v) (v := a),eq,dist_eq_one_iff_adj.mpr adj] at h₂
    rw [eq] at h₁
    have hn := hi.2.2
    rw [eq] at hn
    omega
  let code (i : ℕ) := if i≤s+q.length then i-3 else 2*s+(i-(s+q.length+2))
  have bound (i) (hi : GirthFivePossible r i) : code i < 2*s+(t-1) := by
    have := hi.1; have := hi.2.1
    dsimp [code]; split_ifs with h
    · have := geo i hi h; omega
    · have := forbid i hi; omega
  have inj (i j) (hi : GirthFivePossible r i) (hj : GirthFivePossible r j) (he : code i=code j) : i=j := by
    have := hi.1; have := hj.1; have := forbid i hi; have := forbid j hj
    dsimp [code] at he
    split_ifs at he <;> first | omega | (have := geo i hi (by omega); omega) | (have := geo j hj (by omega); omega)
  have count := ctrl r hr (by omega) code bound inj (fun w => hbr w (Set.mem_univ _))
  have hdx := hmin x
  by_cases ht : 0<t
  · omega
  · have := zero (by omega)
    omega

/-- Every geodesic of length at least five extends, after growing from both
ends, to an induced path of order at least its length plus the minimum degree. -/
theorem girth_five_geodesic_min_degree (hg : 5 ≤ G.egirth) (hc : G.Connected)
    {d : ℕ} (hmin : ∀ x, d ≤ G.degree x) {a v : V} (q : G.Walk a v)
    (hq : q.length=G.dist a v) (hfive : 5 ≤ q.length) : q.length+d ≤ G.path := by
  apply geodesic_growth hc (weight := fun x => G.degree x) _ hmin q hq hfive
  intro u v p hp _ k code bound inj sat
  exact count_slots p hg hc hp code bound inj sat

theorem independent_slot_control (h4 : NoFourCycle G) (hc : G.Connected) :
    GirthFiveSlotControl G (fun x => G.indepNeighborsCard x) := by
  intro u v p hp hn k code bound inj sat
  obtain ⟨W,hW,idx,hi,hp'⟩ := exists_stalled_indep_contacts hc h4 hp hn sat
  let f (w : W) : Fin k := ⟨code (idx w),bound _ (hp' w)⟩
  have fi : Function.Injective f := fun w z e =>
    hi (inj _ _ (hp' w) (hp' z) (congrArg Fin.val e))
  have cnt : W.card ≤ k := by simpa using Fintype.card_le_of_injective f fi
  exact hW.trans (by omega)

theorem geodesic_indep_neighborhood_lower_bound_of_five (h4 : NoFourCycle G) (hc : G.Connected)
    {d : ℕ} (hmin : ∀ x, d ≤ G.indepNeighborsCard x) {a v : V} (q : G.Walk a v)
    (hq : q.length=G.dist a v) (hfive : 5 ≤ q.length) : q.length+d ≤ G.path :=
  geodesic_growth hc (independent_slot_control h4 hc) hmin q hq hfive

end Wall133
