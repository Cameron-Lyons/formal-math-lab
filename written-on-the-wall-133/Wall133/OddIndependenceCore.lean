import Wall133.SimplicialPruning

/-! # Low vertices of an odd neighborhood-independence core -/

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If the removed vertex belongs to a triangle, the two other vertices
retain their edge and lose the unique common neighbor that witnessed its
lower weight. This saves at least one unit of neighborhood independence. -/
theorem sum_indep_delete_strict_of_triangle (h4 : NoFourCycle G) {x y z : V}
    (xy : G.Adj x y) (xz : G.Adj x z) (yz : G.Adj y z) :
    let S := Finset.univ.erase x
    (∑ v,G.indepNeighborsCard v) < (∑ v:S,(G.induce (S:Set V)).indepNeighborsCard v)
      +2*G.indepNeighborsCard x := by
  classical
  let S := Finset.univ.erase x
  let H := G.induce (S:Set V)
  let w := triangleWeight G
  let y' : S := ⟨y, Finset.mem_erase.mpr ⟨xy.ne.symm,Finset.mem_univ _⟩⟩
  let z' : S := ⟨z, Finset.mem_erase.mpr ⟨xz.ne.symm,Finset.mem_univ _⟩⟩
  have no : ¬ ∃ u:S,H.Adj y' u ∧ H.Adj z' u := by
    rintro ⟨u,yu,zu⟩
    exact (Finset.mem_erase.mp u.property).1 (h4 yz.ne yu zu xy.symm xz.symm)
  have improve : w y'.val z'.val < triangleWeight H y' z' := by
    change triangleWeight G y z < triangleWeight H y' z'
    rw [weight_of_triangle_edge yz ⟨x,xy.symm,xz.symm⟩]
    unfold triangleWeight
    rw [if_pos (show H.Adj y' z' from yz)]
    split_ifs with yes
    · exact (no yes).elim
    · decide
  have four : NoFourCycle H := fun _ _ _ _ hne a b c d =>
    Subtype.ext (h4 (fun he => hne (Subtype.ext he)) a b c d)
  have less : (∑ u:S,∑ v:S,w u.val v.val) < ∑ u:S,∑ v:S,triangleWeight H u v := by
    apply Finset.sum_lt_sum
    · intro u _
      exact Finset.sum_le_sum (fun v _ => weight_induce_le S u v)
    · refine ⟨y',Finset.mem_univ _,?_⟩
      exact Finset.sum_lt_sum (fun v _ => weight_induce_le S y' v) ⟨z',Finset.mem_univ _,improve⟩
  have swap (u:S) : (∑ v:S,w u.val v.val)=∑ v∈S,w u.val v := Finset.sum_attach S _
  have sumH (u:S) : (∑ v:S,triangleWeight H u v)=2*H.indepNeighborsCard u := weighted_degree_eq_twice_indep four u
  simp_rw [sumH] at less
  rw [←Finset.mul_sum] at less
  simp_rw [swap] at less
  have massS : mass w S = ∑ u:S,∑ v∈S,w u.val v := (Finset.sum_attach S _).symm
  rw [←massS] at less
  have zero (v:V) : w v v=0 := by simp [w,triangleWeight]
  have decomp := mass_insert (fun a b => weight_symm (G:=G) a b) zero (s:=S)
    (Finset.notMem_erase x Finset.univ)
  change mass w (insert x S)=mass w S+2*∑ v∈S,w x v at decomp
  have cost : (∑ v∈S,w x v)=2*G.indepNeighborsCard x := by
    have he := Finset.sum_erase_add (Finset.univ : Finset V) (w x) (Finset.mem_univ x)
    simpa only [zero,Nat.add_zero,w,weighted_degree_eq_twice_indep h4] using he
  have total : mass w Finset.univ=2*∑ v,G.indepNeighborsCard v := by
    simp only [mass,w,weighted_degree_eq_twice_indep h4,Finset.mul_sum]
  rw [show insert x S=Finset.univ from Finset.insert_erase (Finset.mem_univ x),total,cost] at decomp
  change (∑ v,G.indepNeighborsCard v) < (∑ v:S,H.indepNeighborsCard v)+2*G.indepNeighborsCard x
  omega

omit [DecidableEq V] in
private theorem indep_sum_equiv {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W}
    [DecidableRel H.Adj] (e : G ≃g H) (four : NoFourCycle G) :
    (∑ v,G.indepNeighborsCard v) = ∑ v,H.indepNeighborsCard v := by
  classical
  have h4 : NoFourCycle H := fun x y a b ne xa ya xb yb => by
    apply e.symm.injective
    exact four (fun eq => ne (e.symm.injective eq)) (e.symm.map_rel_iff.2 xa)
      (e.symm.map_rel_iff.2 ya) (e.symm.map_rel_iff.2 xb) (e.symm.map_rel_iff.2 yb)
  have weight (x y:V) : triangleWeight H (e x) (e y)=triangleWeight G x y := by
    have tri : (∃ z,H.Adj (e x) z ∧ H.Adj (e y) z) ↔ ∃ z,G.Adj x z ∧ G.Adj y z := by
      constructor
      · rintro ⟨z,xz,yz⟩
        obtain ⟨z,rfl⟩ := e.surjective z
        exact ⟨z,e.map_rel_iff.mp xz,e.map_rel_iff.mp yz⟩
      · rintro ⟨z,xz,yz⟩
        exact ⟨e z,e.map_rel_iff.mpr xz,e.map_rel_iff.mpr yz⟩
    simp only [triangleWeight,e.map_rel_iff,tri]
    split_ifs <;> rfl
  have eq (x:V) : H.indepNeighborsCard (e x)=G.indepNeighborsCard x := by
    have ss := e.toEquiv.sum_comp (fun y => triangleWeight H (e x) y)
    change (∑ y,triangleWeight H (e x) (e y))=_ at ss
    simp_rw [weight] at ss
    rw [weighted_degree_eq_twice_indep four,weighted_degree_eq_twice_indep h4] at ss
    omega
  have ss := e.toEquiv.sum_comp H.indepNeighborsCard
  change (∑ x,H.indepNeighborsCard (e x))=_ at ss
  simpa only [eq] using ss

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem noFour_induced (h4 : NoFourCycle G) (T : Finset V) : NoFourCycle (G.induce (T:Set V)) :=
  fun _ _ _ _ hne a b c d => Subtype.ext (h4 (fun he => hne (Subtype.ext he)) a b c d)

/-- Choose an induced subgraph of least order carrying the prescribed average.
Its every proper nonempty induced subgraph is strictly below the threshold. -/
theorem exists_minimal_independence_core [Nonempty V] (h4 : NoFourCycle G) {k:ℕ}
    (hav : (k:ℝ)≤l G) : ∃ S : Finset V, S.Nonempty ∧
    k*S.card ≤ ∑ v:S,(G.induce (S:Set V)).indepNeighborsCard v ∧
    ∀ T : Finset S, T.Nonempty → T.card<S.card →
    (∑ v:T,((G.induce (S:Set V)).induce (T:Set S)).indepNeighborsCard v)<k*T.card := by
  classical
  let dense (S : Finset V) := k*S.card ≤ ∑ v:S,(G.induce (S:Set V)).indepNeighborsCard v
  let sets := Finset.univ.filter (fun S : Finset V => S.Nonempty ∧ dense S)
  have mem (S : Finset V) : S∈sets ↔ S.Nonempty ∧ dense S := by simp [sets]
  let un : Finset V := Finset.univ
  let e : G.induce (un:Set V) ≃g G :=
    { toEquiv := { toFun := Subtype.val, invFun := fun x => ⟨x,Finset.mem_univ x⟩,
                   left_inv := fun _ => rfl,right_inv := fun _ => rfl }, map_rel_iff' := Iff.rfl }
  have init : un∈sets := by
    apply (mem un).2
    refine ⟨Finset.univ_nonempty,?_⟩
    change k*un.card≤_
    have eq := indep_sum_equiv e (noFour_induced h4 un)
    have eq' : (∑ v:un,(G.induce (un:Set V)).indepNeighborsCard v)=∑ v,G.indepNeighborsCard v := by
      convert eq using 1
      congr 2
    rw [eq']
    simpa only [un,Finset.card_univ] using le_average_iff_sum_indep.mp hav
  obtain ⟨S,hS,best⟩ := sets.exists_min_image Finset.card ⟨un,init⟩
  obtain ⟨hs,den⟩ := (mem S).1 hS
  refine ⟨S,hs,den,?_⟩
  intro T ht small
  let A := T.map (Function.Embedding.subtype (·∈S))
  have embed : ∀ x:T, x.val.val∈A := fun x => Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩
  let f (x:T) : A := ⟨x.val.val,embed x⟩
  have inj : Function.Injective f := fun x y e => Subtype.ext (Subtype.ext (congrArg (fun a : A => a.val) e))
  have onto : Function.Surjective f := by
    intro y
    obtain ⟨t,ht,eq⟩ := Finset.mem_map.mp y.property
    exact ⟨⟨t,ht⟩,Subtype.ext eq⟩
  let iso : ((G.induce (S:Set V)).induce (T:Set S)) ≃g G.induce (A:Set V) :=
    { toEquiv := Equiv.ofBijective f ⟨inj,onto⟩,map_rel_iff' := Iff.rfl }
  have eq := indep_sum_equiv iso (noFour_induced (noFour_induced h4 S) T)
  have eq' : (∑ u:T,((G.induce (S:Set V)).induce (T:Set S)).indepNeighborsCard u)=∑ v:A,(G.induce (A:Set V)).indepNeighborsCard v := by convert eq using 1 <;> try congr 2
  rw [eq']
  have card : A.card=T.card := Finset.card_map _
  by_contra! high
  have accepted := (mem A).2 ⟨Finset.map_nonempty.mpr ht,(by simpa only [card,dense] using high)⟩
  have := best A accepted
  omega

/-- Deleting an adjacent pair saves its common edge from being counted twice. -/
theorem sum_indep_delete_pair (h4 : NoFourCycle G) {x y : V} (xy : G.Adj x y) :
    let T := (Finset.univ.erase x).erase y
    (∑ v,G.indepNeighborsCard v)+triangleWeight G x y ≤
      (∑ z:T,(G.induce (T:Set V)).indepNeighborsCard z)+2*(G.indepNeighborsCard x+G.indepNeighborsCard y) := by
  classical
  let S := Finset.univ.erase x
  let T := S.erase y
  let H := G.induce (T:Set V)
  let w := triangleWeight G
  have yi : y∈S := Finset.mem_erase.mpr ⟨xy.ne.symm,Finset.mem_univ _⟩
  have zero (v:V) : w v v=0 := by simp [w,triangleWeight]
  have sx := mass_insert (fun a b => weight_symm (G:=G) a b) zero (s:=S) (Finset.notMem_erase x Finset.univ)
  have sy := mass_insert (fun a b => weight_symm (G:=G) a b) zero (s:=T) (Finset.notMem_erase y S)
  have ix : insert x S=Finset.univ := Finset.insert_erase (Finset.mem_univ x)
  have iy : insert y T=S := Finset.insert_erase yi
  change mass w (insert x S)=mass w S+2*∑ v∈S,w x v at sx
  change mass w (insert y T)=mass w T+2*∑ v∈T,w y v at sy
  have total : mass w Finset.univ=2*∑ v,G.indepNeighborsCard v := by
    simp only [mass,w,weighted_degree_eq_twice_indep h4,Finset.mul_sum]
  have cost : (∑ v∈S,w x v)=2*G.indepNeighborsCard x := by
    have he := Finset.sum_erase_add (Finset.univ : Finset V) (w x) (Finset.mem_univ x)
    simpa only [zero,Nat.add_zero,w,weighted_degree_eq_twice_indep h4] using he
  have cmp (u:T) : (∑ v∈T,w u.val v) ≤ 2*H.indepNeighborsCard u := by
    rw [←weighted_degree_eq_twice_indep (noFour_induced h4 T),←Finset.sum_attach T (w u.val)]
    exact Finset.sum_le_sum (fun v _ => weight_induce_le T u v)
  have remain := Finset.sum_le_sum (s:=Finset.univ) (fun (u:T) _ => cmp u)
  have rest : mass w T=∑ u:T,∑ v∈T,w u.val v := (Finset.sum_attach T _).symm
  rw [←Finset.mul_sum,←rest] at remain
  change mass w T≤2*∑ u:T,H.indepNeighborsCard u at remain
  have tY := Finset.sum_erase_add S (w y) yi
  change (∑ v∈T,w y v)+w y y=∑ v∈S,w y v at tY
  rw [zero,Nat.add_zero] at tY
  have dY := Finset.sum_erase_add (Finset.univ:Finset V) (w y) (Finset.mem_univ x)
  change (∑ v∈S,w y v)+w y x=∑ v,w y v at dY
  rw [show w y x=w x y from weight_symm y x,show (∑ v,w y v)=2*G.indepNeighborsCard y from
    weighted_degree_eq_twice_indep h4 y] at dY
  rw [ix,total,cost] at sx
  rw [iy,tY] at sy
  change (∑ v,G.indepNeighborsCard v)+w x y≤(∑ z:T,H.indepNeighborsCard z)+_
  omega

/-- At threshold 2d−1 there is a core of minimum neighborhood independence d
in which an equality vertex lies in no triangle and has no equality neighbor. -/
theorem exists_odd_independence_core [Nonempty V] (h4 : NoFourCycle G) {d : ℕ} (hd : 2≤d)
    (hav : ((2*d-1 : ℕ):ℝ)≤l G) :
    ∃ S : Finset V, S.Nonempty ∧
      (2*d-1)*S.card≤∑ v:S,(G.induce (S:Set V)).indepNeighborsCard v ∧
      (∀ x:S,d≤(G.induce (S:Set V)).indepNeighborsCard x) ∧
      ∀ x:S,(G.induce (S:Set V)).indepNeighborsCard x=d →
        (∀ y z:S,(G.induce (S:Set V)).Adj x y → (G.induce (S:Set V)).Adj x z →
          ¬(G.induce (S:Set V)).Adj y z) ∧
        ∀ y:S,(G.induce (S:Set V)).Adj x y → d<(G.induce (S:Set V)).indepNeighborsCard y := by
  classical
  let k := 2*d-1
  obtain ⟨S,hs,dd,small⟩ := exists_minimal_independence_core (k:=k) h4 hav
  let H := G.induce (S:Set V)
  have four : NoFourCycle H := noFour_induced h4 S
  have : Nonempty S := hs.to_subtype
  have high : ∃ h:S,d<H.indepNeighborsCard h := by
    by_contra! no
    have small := Finset.sum_le_sum (s:=Finset.univ) (g:=fun _ => d) (fun (v:S) _ => no v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at small
    change k*S.card ≤ ∑ v:S,H.indepNeighborsCard v at dd
    have dk : d*S.card < k*S.card := Nat.mul_lt_mul_of_pos_right (by dsimp [k]; omega) hs.card_pos
    rw [Nat.mul_comm d] at dk
    change (∑ i:S,H.indepNeighborsCard i) ≤ S.card*d at small
    exact (dk.not_ge (dd.trans small))
  obtain ⟨h,hh⟩ := high
  have one (x:S) (hx : H.indepNeighborsCard x≤d) :
      (∑ v:(Finset.univ.erase x), (H.induce (↑(Finset.univ.erase x):Set S)).indepNeighborsCard v) + k+1 ≤
        ∑ v:S,H.indepNeighborsCard v := by
    let T := Finset.univ.erase x
    have keep : h∈T := Finset.mem_erase.mpr ⟨fun eq => hh.not_ge (eq ▸ hx),Finset.mem_univ _⟩
    have sz : S.card=T.card+1 := by
      simp only [T,Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Fintype.card_coe]
      have := hs.card_pos; omega
    have low := small T ⟨h,keep⟩ (by omega)
    change (∑ v:T,(H.induce (T:Set S)).indepNeighborsCard v)<k*T.card at low
    change k*S.card≤∑ v:S,H.indepNeighborsCard v at dd
    rw [sz,Nat.mul_succ] at dd
    change (∑ v:T,(H.induce (T:Set S)).indepNeighborsCard v)+k+1≤_
    omega
  have dmin (x:S) : d≤H.indepNeighborsCard x := by
    by_contra! low
    have minimum := one x low.le
    have cut := sum_indep_le_delete_add_twice four x
    change (∑ v:S,H.indepNeighborsCard v)≤(∑ v:(Finset.univ.erase x),
      (H.induce (↑(Finset.univ.erase x):Set S)).indepNeighborsCard v)+2*H.indepNeighborsCard x at cut
    dsimp only [k] at minimum
    omega
  refine ⟨S,hs,dd,dmin,?_⟩
  intro x hx
  change H.indepNeighborsCard x=d at hx
  have noTri (y z:S) (xy:H.Adj x y) (xz:H.Adj x z) : ¬H.Adj y z := by
    intro yz
    have minimum := one x hx.le
    have strict := sum_indep_delete_strict_of_triangle four xy xz yz
    change (∑ v:S,H.indepNeighborsCard v)<(∑ v:(Finset.univ.erase x),
      (H.induce (↑(Finset.univ.erase x):Set S)).indepNeighborsCard v)+2*H.indepNeighborsCard x at strict
    dsimp only [k] at minimum
    omega
  refine ⟨noTri,?_⟩
  intro y xy
  change H.Adj x y at xy
  change d<H.indepNeighborsCard y
  by_contra! hy
  let U := Finset.univ.erase x
  let T := U.erase y
  have xne : h≠x := fun e => hh.not_ge (e ▸ hx.le)
  have yne : h≠y := fun e => hh.not_ge (e ▸ hy)
  have yi : y∈U := Finset.mem_erase.mpr ⟨xy.ne.symm,Finset.mem_univ _⟩
  have keep : h∈T := Finset.mem_erase.mpr ⟨yne,Finset.mem_erase.mpr ⟨xne,Finset.mem_univ _⟩⟩
  have ucard : S.card=U.card+1 := by
    simp only [U,Finset.card_erase_of_mem (Finset.mem_univ x),Finset.card_univ,Fintype.card_coe]
    have := hs.card_pos; omega
  have tcard : U.card=T.card+1 := by
    simp only [T,Finset.card_erase_of_mem yi]
    have := (Finset.card_pos.mpr ⟨y,yi⟩); omega
  have sz : S.card=T.card+1+1 := by omega
  have low := small T ⟨h,keep⟩ (by omega)
  change (∑ v:T,(H.induce (T:Set S)).indepNeighborsCard v)<k*T.card at low
  change k*S.card≤∑ v:S,H.indepNeighborsCard v at dd
  rw [sz,Nat.mul_succ,Nat.mul_succ] at dd
  have pair := sum_indep_delete_pair four xy
  change (∑ v:S,H.indepNeighborsCard v)+triangleWeight H x y≤(∑ v:T,(H.induce (T:Set S)).indepNeighborsCard v)
    +2*(H.indepNeighborsCard x+H.indepNeighborsCard y) at pair
  have w : triangleWeight H x y=2 := by
    unfold triangleWeight
    rw [if_pos xy]
    split_ifs with yes
    · obtain ⟨z,xz,yz⟩ := yes
      exact (noTri y z xy xz yz).elim
    · rfl
  rw [w,hx] at pair
  dsimp only [k] at dd low
  omega

end Wall133
