import Wall133.GeodesicRotation
import Wall133.CoreReturn

/-!
# Extending a rotated path through a nonleaf

If the far vertex of a geodesic has a second neighbor, then it either
extends the rotated path or reaches the dense subgraph again. In the
second case both ends grow from the original geodesic.
-/

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An induced path gains the entire density term whenever a sufficiently
distant vertex of degree at least two is available. -/
theorem distance_add_threshold_le_path_of_nonleaf (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {d e : ℕ} (hd : 4 ≤ d) (he : e ≤ 1)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a : S)
    (hside : ∀ u : S, c u.val=c a.val → d+e ≤ (G.induce (S : Set V)).degree u)
    {v : V} (hD : 5+2*e ≤ G.dist a.val v) (hv : 2 ≤ G.degree v) :
    G.dist a.val v + 2*d+e ≤ G.path+2 := by
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
  have hrev : q.reverse.length=G.dist v a.val := by rw [Walk.length_reverse,hq,G.dist_comm]
  have witness : ∃ n, ∃ T : Chain G n, q.length+2*d+e-3 ≤ n+1 ∧ RetainsGeodesic q S T := by
    rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
    · exact exists_rotated_core_path hc c h4 S hd hmin a q hq (by omega)
    · obtain ⟨n,T,h,hT⟩ := exists_rotated_high_core_path hc c h4 S hd hmin a q hq (by omega) hside
      exact ⟨n,T,by omega,hT⟩
  obtain ⟨n,T,hlen,hT⟩ := witness
  rcases one_step_or_core_return q hq (by omega) hc c h4 S hv T (by omega) hT.suffix hT.inside with
    success | ⟨s,P,hs,hP,hg⟩
  · omega
  rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
  · have := path_bound_of_core_return q.reverse hrev hc c h4 S a.property (by omega : 3 ≤ d)
      hmin (by rw [Walk.length_reverse]; omega) P hP hg (by omega) (j := 2) (by omega)
      (by rw [Walk.length_reverse]; omega)
    rw [Walk.length_reverse] at this
    omega
  · have := path_bound_of_high_core_return q.reverse hrev hc c h4 S a.property hd hmin hside
      (by rw [Walk.length_reverse]; omega) P hP hg (by omega)
    rw [Walk.length_reverse] at this
    omega

/-- The odd core can be anchored in its higher-degree color class. -/
theorem exists_degree_anchor [Nonempty V] (c : G.Coloring (Fin 2)) {k : ℕ} (hk : 7 ≤ k)
    (hav : k*Fintype.card V ≤ ∑ v, G.degree v) :
    ∃ (S : Finset V) (a : S), (∀ u : S, k/2+1 ≤ (G.induce (S : Set V)).degree u) ∧
      ∀ u : S, c u.val=c a.val → k/2+1+k%2 ≤ (G.induce (S : Set V)).degree u := by
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · obtain ⟨S,⟨a,ha⟩,hm⟩ := exists_degree_core G (by omega : 0 < k) hav
    exact ⟨S,⟨a,ha⟩,hm,fun u _ => by simpa [h] using hm u⟩
  · have he : 2*(k/2)+1=k := by omega
    obtain ⟨col,S,⟨b,hb⟩,hm⟩ := exists_odd_degree_core c (by omega : 0<k/2) (by rw [he]; exact hav)
    have base (u : S) : k/2+1 ≤ (G.induce (S : Set V)).degree u := (Nat.le_add_right _ _).trans (hm u)
    have ex : ∃ a : S, c a.val=col := by
      by_cases hb' : c b=col
      · exact ⟨⟨b,hb⟩,hb'⟩
      · let b' : S := ⟨b,hb⟩
        obtain ⟨a,ha⟩ := ((G.induce (S : Set V)).degree_pos_iff_exists_adj b').mp
          (by have := base b'; omega)
        refine ⟨a,Fin.ext ?_⟩
        have := Fin.val_ne_of_ne hb'
        have := Fin.val_ne_of_ne (c.valid (show G.Adj b a.val from ha))
        have := (c b).isLt
        have := (c a.val).isLt
        have := col.isLt
        omega
    obtain ⟨a,ha⟩ := ex
    refine ⟨S,a,base,fun u hu => ?_⟩
    simpa only [if_pos (hu.trans ha),h] using hm u

/-- The floored conjecture holds at every radius if all but at most one
vertex have degree at least two. -/
theorem radius_add_floor_le_path_of_at_most_one_leaf [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (e : V) (hdegree : ∀ v, v ≠ e → 2 ≤ G.degree v) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  by_cases hr : G.radius.toNat ≤ 6
  · exact radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr
  by_contra! hbad
  let k := ⌊l G⌋₊
  change G.path < G.radius.toNat+k at hbad
  have hk : 7 ≤ k := by have := chung_bound_nat G hc; omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (div_nonneg
    (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _))
  obtain ⟨c⟩ := hb
  obtain ⟨S,a,hmin,hside⟩ := exists_degree_anchor c hk (sum_degree_ge_of_le_l hav)
  obtain ⟨a',hcol,ha⟩ := exists_nearby_anchor hc c h4 S a e (by omega) hbad hmin
  obtain ⟨v,q,hq,hrv⟩ := exists_geodesic_ge_radius G hc a'.val
  have hv : v ≠ e := by intro he; subst v; omega
  have h := distance_add_threshold_le_path_of_nonleaf hc c h4 S (d := k/2+1) (e := k%2)
    (by omega) (by omega) hmin a' (by simpa only [hcol] using hside)
    (v := v) (by omega) (hdegree v hv)
  omega

end Wall133
