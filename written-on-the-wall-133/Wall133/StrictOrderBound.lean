module

public import Wall133.OrderBound

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A second neighbor of the last vertex of a geodesic supplies a further
vertex at distance at least three from its starting vertex. -/
theorem neighbor_independence_sum_add_radius_of_two_le_degree (hc : G.Connected)
    (h4 : NoFourCycle G) (hr : 4≤G.radius.toNat) (hmin : ∀ v,2≤G.degree v) (v : V) :
    (∑ w∈G.neighborFinset v,G.indepNeighborsCard w)+(G.radius.toNat-1)<Fintype.card V := by
  classical
  obtain ⟨a,q,hq,large⟩ := exists_geodesic_ge_radius G hc v
  let I := Finset.Icc 3 q.length
  let T := I.image q.getVert
  have inj : Set.InjOn q.getVert (↑I) := fun i hi j hj =>
    (q.isPath_of_length_eq_dist hq).getVert_injOn (Finset.mem_Icc.mp hi).2 (Finset.mem_Icc.mp hj).2
  have size : T.card=q.length+1-3 := by
    rw [show T=I.image q.getVert from rfl,Finset.card_image_of_injOn inj]
    exact Nat.card_Icc _ _
  let N := (G.neighborFinset a).erase (q.getVert (q.length-1))
  have more : N.Nonempty := Finset.card_pos.mp (by
    have h := Finset.pred_card_le_card_erase (s:=G.neighborFinset a) (a:=q.getVert (q.length-1))
    rw [G.card_neighborFinset_eq_degree] at h
    have := hmin a
    change 0<(Finset.erase _ _).card
    omega)
  obtain ⟨z,hz⟩ := more
  obtain ⟨neq,mem⟩ := Finset.mem_erase.mp hz
  have az := (G.mem_neighborFinset _ _).1 mem
  have out : z∉T := by
    intro he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have h := (adj_getVert_iff_consecutive_of_length_eq_dist q hq (i:=i) (j:=q.length)
      (Finset.mem_Icc.mp hi).2 le_rfl).1 (by simpa using az.symm)
    have limit := (Finset.mem_Icc.mp hi).2
    exact neq (congrArg q.getVert (by omega))
  have far (u) (hu : u∈insert z T) : 3≤G.dist v u := by
    rcases Finset.mem_insert.mp hu with rfl|ht
    · have tri := hc.dist_triangle (u:=v) (v:=u) (w:=a)
      rw [dist_eq_one_iff_adj.mpr az.symm] at tri
      omega
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨lo,top⟩ := Finset.mem_Icc.mp hi
      have d : G.dist v (q.getVert i)=i := by
        simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le i) top
      omega
  have count := neighbor_independence_sum_add_far h4 v (insert z T) (fun u hu => by
    have dist := far u hu
    refine ⟨?_,?_,?_⟩
    · rintro rfl; simp at dist
    · intro edge; rw [dist_eq_one_iff_adj.mpr edge] at dist; omega
    · intro w vw wu
      have tri := hc.dist_triangle (u:=v) (v:=w) (w:=u)
      rw [dist_eq_one_iff_adj.mpr vw,dist_eq_one_iff_adj.mpr wu] at tri
      omega)
  rw [Finset.card_insert_of_notMem out,size] at count
  omega

omit [DecidableEq V] in
private theorem square_excess (f : V → ℕ) {k : ℕ} (first : k*Fintype.card V ≤ ∑ v,f v) (x : V) :
    (Fintype.card V : ℤ)*k^2 + ((f x : ℤ)-k)^2 ≤ ((∑ v,f v^2 : ℕ) : ℤ) := by
  let g (v : V) : ℤ := f v
  have total : (k : ℤ)*Fintype.card V ≤ ∑ v,g v := by dsimp [g]; exact_mod_cast first
  have second : ((∑ v,f v^2 : ℕ) : ℤ) = ∑ v,g v^2 := by simp [g]
  have expand (v : V) : (g v-k)^2 = g v^2 - 2*(k:ℤ)*g v + k^2 := by ring
  have sum : ∑ v,(g v-k)^2 = (∑ v,g v^2) - 2*(k:ℤ)*(∑ v,g v) + Fintype.card V*k^2 := by
    simp_rw [expand]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_const,Finset.card_univ]
    simp only [nsmul_eq_mul]
  have term := Finset.single_le_sum (s:=Finset.univ) (f:=fun v => (g v-k)^2)
    (fun v _ => sq_nonneg _) (Finset.mem_univ x)
  have scaled := mul_le_mul_of_nonneg_left total (by positivity : 0≤2*(k:ℤ))
  rw [second]
  change (Fintype.card V : ℤ)*k^2+(g x-k)^2≤_
  nlinarith only [sum,term,scaled]

/-- When the radius is between four and the integer threshold k≥5, the
presence of a vertex below that threshold forces at least k²+radius+1 vertices. -/
theorem sq_add_radius_add_one_le_order_of_independence_defect [Nonempty V] (hc : G.Connected)
    (h4 : NoFourCycle G) {k : ℕ} (hk : 5≤k) (hr : 4≤G.radius.toNat) (hrk : G.radius.toNat≤k)
    (avg : (k:ℝ)≤l G) {x : V} (low : G.indepNeighborsCard x<k) :
    k^2+G.radius.toNat+1 ≤ Fintype.card V := by
  classical
  let f := G.indepNeighborsCard
  let n := Fintype.card V
  let row (v : V) := ∑ w∈G.neighborFinset v,f w
  let second := ∑ v,f v^2
  have initial := sq_add_radius_le_order_of_independence_defect hc h4 avg low
  by_contra! fail
  have size : n=k^2+G.radius.toNat := by dsimp [n]; omega
  have first : k*n ≤ ∑ v,f v := le_average_iff_sum_indep.mp avg
  have variance (v : V) : (n:ℤ)*k^2+((f v:ℤ)-k)^2 ≤ (second:ℤ) := square_excess f first v
  have localBound (v : V) : row v ≤ k^2+1 := by
    have := neighbor_independence_sum_add_radius hc h4 v
    change row v+(G.radius.toNat-2)<n at this
    omega
  have byRows : second ≤ ∑ v,row v := by
    rw [←sum_degree_times_independence_eq (G:=G)]
    apply Finset.sum_le_sum
    intro v _
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (indepNeighborsCard_le_degree _)
  by_cases two : ∀ v,2≤G.degree v
  · have bound (v) : row v≤k^2 := by
      have h := neighbor_independence_sum_add_radius_of_two_le_degree hc h4 hr two v
      change row v+(G.radius.toNat-1)<n at h
      omega
    have cap : second ≤ n*k^2 := by
      apply byRows.trans
      exact (Finset.sum_le_sum (s:=Finset.univ) (fun v _ => bound v)).trans_eq (by simp [n])
    have cap' : (second:ℤ) ≤ (n:ℤ)*k^2 := by exact_mod_cast cap
    have inequ : (f x:ℤ) ≠ k := by exact_mod_cast (Nat.ne_of_lt low)
    linarith [variance x,sq_pos_of_ne_zero (sub_ne_zero.mpr inequ)]
  · push Not at two
    obtain ⟨z,hz⟩ := two
    have one : f z≤1 := (indepNeighborsCard_le_degree z).trans (by omega)
    have cap : second ≤ n*(k^2+1) := by
      apply byRows.trans
      exact (Finset.sum_le_sum (s:=Finset.univ) (fun v _ => localBound v)).trans_eq (by simp [n])
    have cap' : (second:ℤ) ≤ (n:ℤ)*(k^2+1) := by exact_mod_cast cap
    have size' : (n:ℤ)=(k:ℤ)^2+G.radius.toNat := by exact_mod_cast size
    have rad : (G.radius.toNat:ℤ)≤k := by exact_mod_cast hrk
    have k5 : (5:ℤ)≤k := by exact_mod_cast hk
    have maxf (v) : f v≤2*k := by
      by_contra! h
      have hi : 2*(k:ℤ)+1 ≤ f v := by exact_mod_cast h
      have squares := sq_le_sq' (a := (k:ℤ)+1) (b := (f v:ℤ)-k) (by omega) (by omega)
      nlinarith only [squares,variance v,cap',size',rad,k5]
    have smallRow : row z≤2*k := by
      have h := Finset.sum_le_sum (s:=G.neighborFinset z) (fun v _ => maxf v)
      rw [Finset.sum_const,nsmul_eq_mul,G.card_neighborFinset_eq_degree] at h
      change row z ≤ G.degree z*(2*k) at h
      exact h.trans (by simpa using (Nat.mul_le_mul_right (2*k) (show G.degree z≤1 by omega)))
    have erase := Finset.sum_le_sum (s:=Finset.univ.erase z) (fun v _ => localBound v)
    rw [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ z),Finset.card_univ] at erase
    change (∑ v∈Finset.univ.erase z,row v) ≤ (n-1)*(k^2+1) at erase
    have er := Finset.sum_erase_add (s:=Finset.univ) row (Finset.mem_univ z)
    have final : second ≤ (n-1)*(k^2+1)+2*k := by omega
    have npos : 0<n := Fintype.card_pos
    have minus : ((n-1:ℕ):ℤ)=n-1 := by rw [Nat.cast_sub (by omega : 1≤n)]; rfl
    have final' : (second:ℤ) ≤ ((n:ℤ)-1)*((k:ℤ)^2+1)+2*k := by
      rw [←minus]; exact_mod_cast final
    have one' : (f z:ℤ)≤1 := by exact_mod_cast one
    have squares := sq_le_sq' (a := (k:ℤ)-1) (b := (k:ℤ)-f z) (by omega) (by omega)
    have poly : 0≤((k:ℤ)-5)*k := mul_nonneg (by omega) (by positivity)
    nlinarith only [squares,variance z,final',size',rad,poly]

end Wall133
