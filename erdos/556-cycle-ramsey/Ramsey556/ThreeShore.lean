import Ramsey556.BicliqueObstruction

namespace Ramsey556.BicliqueObstruction

private def pair (a b x y : Fin 6) : Bool := (a==x && b==y) || (a==y && b==x)

/-- The three common neighbors are 0,1,2. The six positions in their
opposite shore are numbered 3 through 8, with fixed red pairs 3–4 and 5–6. -/
private def cycleOrder (u v : Fin 6) : Vector (Fin 9) 9 :=
  if pair u v 1 3 then #v[0,3,4,6,5,1,7,2,8]
  else if pair u v 1 4 then #v[0,3,4,7,1,5,6,2,8]
  else if pair u v 1 5 then #v[0,3,4,8,1,5,6,2,7]
  else if pair u v 3 4 then #v[0,5,6,7,1,3,4,2,8]
  else if pair u v 3 5 then #v[0,5,6,8,1,3,4,2,7]
  else #v[0,3,4,1,5,6,2,7,8]

private def permitted (u v : Fin 6) : Fin 3 ⊕ Fin 6 → Fin 3 ⊕ Fin 6 → Bool
  | .inl _, .inr _ | .inr _, .inl _ => true
  | .inr i,.inr j => pair i j 0 1 || pair i j 2 3 || pair i j u v
  | _,_ => false

private def decode (i : Fin 9) : Fin 3 ⊕ Fin 6 :=
  if h : i.val<3 then .inl ⟨i.val,h⟩ else .inr ⟨i.val-3,by omega⟩

set_option synthInstance.maxSize 4096 in
private theorem order_valid : ∀ u v : Fin 6, u≠v → u≠0 → u≠2 → v≠0 → v≠2 →
    (∀ i j : Fin 9, decode (cycleOrder u v)[i] = decode (cycleOrder u v)[j] → i=j) ∧
    ∀ i : Fin 9, permitted u v (decode (cycleOrder u v)[i]) (decode (cycleOrder u v)[i+1]) = true := by
  decide +kernel

private theorem threeEdges {n : Nat} (c : Coloring n) (r : Fin 3)
    (a : Fin 3 → Fin n) (b : Fin 6 → Fin n)
    (ai : ∀ ⦃i j⦄, a i=a j → i=j) (bi : ∀ ⦃i j⦄, b i=b j → i=j)
    (apart : ∀ i j, a i≠b j) (cross : ∀ i j, c.edge (a i) (b j)=r)
    {u v : Fin 6} (ne : u≠v) (u0 : u≠0) (u2 : u≠2) (v0 : v≠0) (v2 : v≠2)
    (one : c.edge (b 0) (b 1)=r) (two : c.edge (b 2) (b 3)=r)
    (extra : c.edge (b u) (b v)=r) : HasMonoC9 c := by
  let f := Sum.elim a b
  have inj : ∀ i j, f i=f j → i=j := by
    rintro (i|i) (j|j) e
    · exact congrArg Sum.inl (ai e)
    · exact (apart _ _ e).elim
    · exact (apart _ _ e.symm).elim
    · exact congrArg Sum.inr (bi e)
  have edge (i j : Fin 3 ⊕ Fin 6) (e : permitted u v i j = true) : c.edge (f i) (f j)=r := by
    cases i with
    | inl i =>
      cases j with
      | inl j => contradiction
      | inr j => exact cross _ _
    | inr i =>
      cases j with
      | inl j => exact (c.symm _ _).trans (cross _ _)
      | inr j =>
        simp only [permitted,pair,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at e
        rcases e with (((⟨rfl,rfl⟩|⟨rfl,rfl⟩)|(⟨rfl,rfl⟩|⟨rfl,rfl⟩))|(⟨rfl,rfl⟩|⟨rfl,rfl⟩)) <;>
          first | assumption | exact (c.symm _ _).trans one | exact (c.symm _ _).trans two |
                  exact (c.symm _ _).trans extra
  obtain ⟨oi,ok⟩ := order_valid u v ne u0 u2 v0 v2
  exact ⟨r,fun i => f (decode (cycleOrder u v)[i]),fun {_ _} e => oi _ _ (inj _ _ e),
    fun i => edge _ _ (ok i)⟩

private theorem outside {α : Type} (xs used : List α) (nd : xs.Nodup)
    (big : used.length < xs.length) : ∃ z ∈ xs, z ∉ used := by
  apply Classical.byContradiction; intro none
  have le := nd.length_le_of_subset (l₂ := used) (fun {z} hz =>
    Classical.byContradiction (fun hn => none ⟨z,hz,hn⟩))
  omega

/-- Without an independent m-set in color r, a monochromatic K₃,ₘ₊₂
forces a C₉. Two disjoint r-edges exist in the large shore. A third edge
avoiding one chosen endpoint of each forms a linear forest of three edges.
The three common neighbors join its path components into a nine-cycle. -/
theorem hasMonoC9_of_three_shore_on {n m : Nat} (c : Coloring n) (r : Fin 3)
    (enough : 6 ≤ m) (a : Fin 3 → Fin n) (b : Fin (m+2) → Fin n)
    (ai : ∀ ⦃i j⦄, a i=a j → i=j) (bi : ∀ ⦃i j⦄, b i=b j → i=j)
    (apart : ∀ i j, a i≠b j) (cross : ∀ i j, c.edge (a i) (b j)=r)
    (hit : ∀ v : Fin m → Fin n, (∀ ⦃i j⦄, v i=v j → i=j) → (∀ i, ∃ j, v i=b j) →
      ∃ i j, i≠j ∧ c.edge (v i) (v j)=r) : HasMonoC9 c := by
  let base := (List.finRange (m+2)).map b
  have nd : base.Nodup := (List.nodup_finRange _).map b (fun _ _ sep e => sep (bi e))
  have size : base.length=m+2 := by simp [base]
  have pick (xs : List (Fin n)) (sub : xs ⊆ base) := pickEdgeOn c r xs
    (fun v vi mem => hit v vi (fun i => by
      obtain ⟨j,_,e⟩ := List.mem_map.mp (sub (mem i))
      exact ⟨j,e.symm⟩))
  obtain ⟨p,hp,q,hq,pq,pqe,xs,nx,lx,fresh⟩ := pick base (fun {_} h => h) nd (by omega)
  obtain ⟨s,hs,t,ht,st,ste,_⟩ := pick xs (fun {_} h => (fresh _ h).2.2) nx (by omega)
  obtain ⟨sp,sq,sbase⟩ := fresh s hs
  obtain ⟨tp,tq,tbase⟩ := fresh t ht
  let ys := (base.erase p).erase s
  have s1 := nd.mem_erase_iff.mpr ⟨sp,sbase⟩
  have ly : m ≤ ys.length := by
    simp only [ys,List.length_erase_of_mem hp,List.length_erase_of_mem s1]
    omega
  obtain ⟨u,hu,v,hv,uv,uve,_⟩ := pick ys (fun {_} h => List.mem_of_mem_erase (List.mem_of_mem_erase h)) ((nd.erase _).erase _) ly
  have valid (j) (mem : j ∈ ys) : j≠p ∧ j≠s ∧ j ∈ base := by
    obtain ⟨js,rem⟩ := (nd.erase _).mem_erase_iff.mp mem
    obtain ⟨jp,keep⟩ := nd.mem_erase_iff.mp rem
    exact ⟨jp,js,keep⟩
  obtain ⟨up,us,ubase⟩ := valid _ hu
  obtain ⟨vp,vs,vbase⟩ := valid _ hv
  obtain ⟨x,hx,newx⟩ := outside base [p,q,s,t,u,v] nd (by simp; omega)
  obtain ⟨y,hy,newy⟩ := outside base [p,q,s,t,u,v,x] nd (by simp; omega)
  let U := if u=q ∨ u=t then x else u
  let V := if v=q ∨ v=t then y else v
  let vertices := [p,q,s,t,U,V]
  have nodup : vertices.Nodup := by
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or] at newx newy
    simp only [vertices,List.nodup_cons,List.nodup_nil,List.mem_cons,List.mem_nil_iff,not_or,or_false,and_true]
    dsimp [U,V]
    split <;> split <;> grind
  let f (i : Fin 6) : Fin n := vertices[i.val]'i.isLt
  have fi : ∀ ⦃i j⦄, f i=f j → i=j := fun {_ _} e => Fin.ext (nodup.eq_of_getElem_eq _ _ e)
  have mem (i : Fin 6) : f i ∈ base := by
    have h : f i ∈ vertices := List.getElem_mem ..
    simp only [vertices,List.mem_cons,List.mem_nil_iff,or_false] at h
    have mU : U∈base := by dsimp [U]; split <;> assumption
    have mV : V∈base := by dsimp [V]; split <;> assumption
    rcases h with e|e|e|e|e|e <;> rw [e] <;> assumption
  let iu : Fin 6 := if u=q then 1 else if u=t then 3 else 4
  let iv : Fin 6 := if v=q then 1 else if v=t then 3 else 5
  have getu : f iu=u := by by_cases h : u=q <;> by_cases k : u=t <;> simp [f,iu,vertices,U,h,k,tq] <;> rfl
  have getv : f iv=v := by by_cases h : v=q <;> by_cases k : v=t <;> simp [f,iv,vertices,V,h,k,tq] <;> rfl
  apply threeEdges c r a f (@ai) (@fi)
  · intro i j
    obtain ⟨z,_,h⟩ := List.mem_map.mp (mem j)
    exact h ▸ apart i z
  · intro i j
    obtain ⟨z,_,h⟩ := List.mem_map.mp (mem j)
    exact h ▸ cross i z
  · exact fun e : iu=iv => uv (getu.symm.trans ((congrArg f e).trans getv))
  · dsimp [iu]; split <;> first | decide | (split <;> decide)
  · dsimp [iu]; split <;> first | decide | (split <;> decide)
  · dsimp [iv]; split <;> first | decide | (split <;> decide)
  · dsimp [iv]; split <;> first | decide | (split <;> decide)
  · exact pqe
  · exact ste
  · rwa [getu,getv]

theorem hasMonoC9_of_three_shore {n m : Nat} (c : Coloring n) (r : Fin 3)
    (enough : 6 ≤ m) (a : Fin 3 → Fin n) (b : Fin (m+2) → Fin n)
    (ai : ∀ ⦃i j⦄, a i=a j → i=j) (bi : ∀ ⦃i j⦄, b i=b j → i=j)
    (apart : ∀ i j, a i≠b j) (cross : ∀ i j, c.edge (a i) (b j)=r)
    (hit : ∀ v : Fin m → Fin n, (∀ ⦃i j⦄, v i=v j → i=j) →
      ∃ i j, i≠j ∧ c.edge (v i) (v j)=r) : HasMonoC9 c :=
  hasMonoC9_of_three_shore_on c r enough a b (@ai) (@bi) apart cross (fun v vi _ => hit v vi)

end Ramsey556.BicliqueObstruction
