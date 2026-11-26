module

public import Wall133.DiameterTwoDensity

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A geodesic from v has at least radius minus two vertices outside
the closed two-step neighborhood of v. -/
theorem neighbor_independence_sum_add_radius (hc : G.Connected) (h4 : NoFourCycle G) (v : V) :
    (∑ w∈G.neighborFinset v,G.indepNeighborsCard w)+(G.radius.toNat-2) < Fintype.card V := by
  classical
  obtain ⟨a,q,hq,hr⟩ := exists_geodesic_ge_radius G hc v
  let I := Finset.Icc 3 q.length
  let T := I.image q.getVert
  have inject : Set.InjOn q.getVert (↑I) := fun i hi j hj =>
    (q.isPath_of_length_eq_dist hq).getVert_injOn (Finset.mem_Icc.mp hi).2 (Finset.mem_Icc.mp hj).2
  have size : T.card=q.length+1-3 := by
    rw [show T=I.image q.getVert from rfl,Finset.card_image_of_injOn inject]; exact Nat.card_Icc _ _
  have far (x) (hx : x∈T) : x≠v ∧ ¬G.Adj v x ∧ ∀ w,G.Adj v w → ¬G.Adj w x := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨lo,top⟩ := Finset.mem_Icc.mp hi
    have dist : G.dist v (q.getVert i)=i := by
      simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) top
    refine ⟨?_,?_,?_⟩
    · intro e; rw [e,dist_self] at dist; omega
    · intro edge; rw [dist_eq_one_iff_adj.mpr edge] at dist; omega
    · intro w vw wx
      have tri := hc.dist_triangle (u:=v) (v:=w) (w:=q.getVert i)
      rw [dist,dist_eq_one_iff_adj.mpr vw,dist_eq_one_iff_adj.mpr wx] at tri
      omega
  have := neighbor_independence_sum_add_far h4 v T far
  omega

omit [DecidableEq V] in
/-- Count a neighbor's independence number once for each incident edge. -/
theorem sum_degree_times_independence_eq :
    (∑ w, G.degree w * G.indepNeighborsCard w) =
      ∑ v, ∑ w∈G.neighborFinset v,G.indepNeighborsCard w := by
  classical
  let f := G.indepNeighborsCard
  have factor (w : V) :
      (∑ v, if G.Adj v w then f w else 0) = G.degree w * f w := by
    simp_rw [G.adj_comm (u:=_) (v:=w)]
    rw [← Finset.sum_filter]
    have eq : Finset.univ.filter (G.Adj w) = G.neighborFinset w := by ext; simp
    rw [eq,Finset.sum_const,G.card_neighborFinset_eq_degree, nsmul_eq_mul]
    rfl
  have distribute (v : V) :
      (∑ w, if G.Adj v w then f w else 0) = ∑ w∈G.neighborFinset v, f w := by
    rw [← Finset.sum_filter]
    congr 1
    ext; simp
  change (∑ w,G.degree w * f w) = _
  simp_rw [←factor]
  rw [Finset.sum_comm]
  simp_rw [distribute]
  rfl

omit [DecidableEq V] in
private theorem sum_degree_times_independence {b : ℕ}
    (bound : ∀ v, (∑ w∈G.neighborFinset v,G.indepNeighborsCard w)≤b) :
    (∑ w, G.degree w * G.indepNeighborsCard w) ≤ Fintype.card V*b := by
  rw [sum_degree_times_independence_eq]
  calc
    _ ≤ ∑ _v : V, b := Finset.sum_le_sum (fun v _ => bound v)
    _ = _ := by simp

/-- A vertex below an integer threshold attained on average makes the
second moment strictly greater than the square of that threshold. The
geodesic bound on two-step neighborhoods then gives the order estimate. -/
theorem sq_add_radius_le_order_of_independence_defect [Nonempty V] (hc : G.Connected)
    (h4 : NoFourCycle G) {k : ℕ} (avg : (k:ℝ) ≤ l G) {x : V} (low : G.indepNeighborsCard x < k) :
    k^2+(G.radius.toNat-2)+2 ≤ Fintype.card V := by
  classical
  let f := G.indepNeighborsCard
  let n := Fintype.card V
  let b := n-(G.radius.toNat-2)-1
  have bound (v) : (∑ w∈G.neighborFinset v,G.indepNeighborsCard w) ≤ b := by
    have := neighbor_independence_sum_add_radius hc h4 v
    dsimp [b,n]; omega
  have count := sum_degree_times_independence bound
  have second : ∑ v,f v ^ 2 ≤ n*b := by
    refine le_trans (Finset.sum_le_sum (g:=fun v => G.degree v * f v) (fun v _ => ?_)) count
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (indepNeighborsCard_le_degree _)
  have convex (v : V) : 2*k*f v ≤ (f v)^2+k^2 := by
    have real : 2*(k:ℝ)*(f v:ℝ) ≤ (f v:ℝ)^2+(k:ℝ)^2 := by nlinarith [sq_nonneg ((f v:ℝ)-k)]
    exact_mod_cast real
  have strict : 2*k*f x < (f x)^2+k^2 := by
    have h : (f x:ℝ)<k := by exact_mod_cast low
    have pos := sq_pos_of_ne_zero (sub_ne_zero.mpr h.ne)
    exact_mod_cast (show 2*(k:ℝ)*(f x:ℝ)<(f x:ℝ)^2+(k:ℝ)^2 by nlinarith)
  have variance := Finset.sum_lt_sum (s:=Finset.univ) (fun v _ => convex v) ⟨x,Finset.mem_univ _,strict⟩
  rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at variance
  change 2*k * (∑ v,f v) < (∑ v,f v^2) + n*k^2 at variance
  have first : k*n ≤ ∑ v,f v := le_average_iff_sum_indep.mp avg
  have lhs := Nat.mul_le_mul_left (2*k) first
  rw [show 2*k*(k*n) = n*k^2 + n*k^2 by ring] at lhs
  have gap : n*k^2 < n*b := by omega
  have := (Nat.lt_of_mul_lt_mul_left gap)
  change k^2+(G.radius.toNat-2)+2 ≤ n
  dsimp [b] at this
  omega

end Wall133
