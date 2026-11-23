import Ramsey556.Certified16
import Ramsey556.TwoVertex

namespace Ramsey556.BicliqueObstruction

private def swap16 (x y i : Fin 16) : Fin 16 := if i = x then y else if i = y then x else i

private def ends (x y : Fin 16) (i : Fin 5) : Fin 16 :=
  swap16 0 x (swap16 4 (swap16 0 x y) ⟨i.val, by omega⟩)

private theorem ends_spec : ∀ x y : Fin 16, x ≠ y →
    ends x y 0 = x ∧ ends x y 4 = y ∧ ∀ i j, ends x y i = ends x y j → i = j := by
  decide +kernel

/-- Four common neighbors join any two out of five other vertices by
an alternating path of length eight. An edge joining its ends closes C₉. -/
theorem closeAcross (c : Coloring 33) (r : Fin 3) (a : Fin 4 → Fin 33) (b : Fin 5 → Fin 33)
    (ha : ∀ ⦃i j⦄, a i = a j → i = j) (hb : ∀ ⦃i j⦄, b i = b j → i = j)
    (disj : ∀ i j, a i ≠ b j) (cross : ∀ i j, c.edge (a i) (b j) = r)
    (inside : c.edge (b 0) (b 4) = r) : HasMonoC9 c := by
  let v (i : Fin 9) := if h : i.val % 2 = 0 then b ⟨i.val/2, by omega⟩
    else a ⟨i.val/2, by omega⟩
  refine ⟨r,v,?_,?_⟩
  · intro i j e
    simp only [v] at e
    split at e <;> split at e
    · have := congrArg Fin.val (hb e)
      apply Fin.ext; dsimp at this; omega
    · exact (disj _ _ e.symm).elim
    · exact (disj _ _ e).elim
    · have := congrArg Fin.val (ha e)
      apply Fin.ext; dsimp at this; omega
  · intro i
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact cross _ _ | exact (c.symm _ _).trans (cross _ _) | exact (c.symm _ _).trans inside

/-- A monochromatic K₄,₁₆ forces a monochromatic nine-cycle in K₃₃. -/
theorem hasMonoC9_of_four_sixteen (c : Coloring 33) (r : Fin 3)
    (a : Fin 4 → Fin 33) (b : Fin 16 → Fin 33)
    (ha : ∀ ⦃i j⦄, a i = a j → i = j) (hb : ∀ ⦃i j⦄, b i = b j → i = j)
    (disj : ∀ i j, a i ≠ b j) (red : ∀ i j, c.edge (a i) (b j) = r) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  apply free
  apply hasMonoC9_of_independent16 twoColorOctets16 c b (@hb) r
  intro x y ne edge
  obtain ⟨head,tail,inj⟩ := ends_spec x y ne
  apply free
  exact closeAcross c r a (fun i => b (ends x y i)) (@ha) (fun {_ _} e => inj _ _ (hb e))
    (fun i j => disj i _) (fun i j => red i _) (by simpa only [head,tail] using edge)

theorem pickEdgeOn {n m : Nat} (c : Coloring n) (r : Fin 3)
    (xs : List (Fin n)) (hit : ∀ v : Fin m → Fin n, (∀ ⦃i j⦄, v i=v j → i=j) → (∀ i, v i∈xs) →
      ∃ i j, i≠j ∧ c.edge (v i) (v j)=r)
    (nd : xs.Nodup) (enough : m ≤ xs.length) :
    ∃ x ∈ xs, ∃ y ∈ xs, x≠y ∧ c.edge x y=r ∧ ∃ rest : List (Fin n), rest.Nodup ∧
      rest.length+2=xs.length ∧ ∀ u ∈ rest, u≠x ∧ u≠y ∧ u ∈ xs := by
  let f (i : Fin m) := xs[i.val]'(by omega)
  have fi : ∀ ⦃i j⦄, f i=f j → i=j := fun {_ _} e => Fin.ext (nd.eq_of_getElem_eq _ _ e)
  have mem (i) : f i ∈ xs := List.getElem_mem ..
  obtain ⟨i,j,ne,edge⟩ := hit f fi mem
  have ne' : f i≠f j := fun e => ne (fi e)
  have jmem := nd.mem_erase_iff.mpr ⟨ne'.symm,mem j⟩
  refine ⟨f i,mem i,f j,mem j,ne',edge,(xs.erase (f i)).erase (f j),(nd.erase _).erase _,?_,?_⟩
  · have h1 := List.length_erase_of_mem (mem i)
    have h2 := List.length_erase_of_mem jmem
    have h3 := List.length_pos_of_mem jmem
    omega
  · intro u hu
    obtain ⟨a,h⟩ := (nd.erase _).mem_erase_iff.mp hu
    obtain ⟨b,h'⟩ := nd.mem_erase_iff.mp h
    exact ⟨b,a,h'⟩

theorem pickEdge {n m : Nat} (c : Coloring n) (r : Fin 3)
    (hit : ∀ v : Fin m → Fin n, (∀ ⦃i j⦄, v i=v j → i=j) →
      ∃ i j, i≠j ∧ c.edge (v i) (v j)=r)
    (xs : List (Fin n)) (nd : xs.Nodup) (enough : m ≤ xs.length) :
    ∃ x ∈ xs, ∃ y ∈ xs, x≠y ∧ c.edge x y=r ∧ ∃ rest : List (Fin n), rest.Nodup ∧
      rest.length+2=xs.length ∧ ∀ u ∈ rest, u≠x ∧ u≠y ∧ u ∈ xs :=
  pickEdgeOn c r xs (fun v vi _ => hit v vi) nd enough

/-- Three distinct matching edges in one shore form a nine-cycle by
inserting one of the three common neighbors after each matching edge. -/
theorem hasMonoC9_of_three_matching {n m : Nat} (c : Coloring n) (r : Fin 3)
    (a : Fin 3 → Fin n) (b : Fin (m+4) → Fin n)
    (ha : ∀ ⦃i j⦄, a i = a j → i = j) (hb : ∀ ⦃i j⦄, b i = b j → i = j)
    (disj : ∀ i j, a i ≠ b j) (cross : ∀ i j, c.edge (a i) (b j) = r)
    (hit : ∀ v : Fin m → Fin n, (∀ ⦃i j⦄, v i=v j → i=j) →
      ∃ i j, i≠j ∧ c.edge (v i) (v j)=r) : HasMonoC9 c := by
  let base := (List.finRange (m+4)).map b
  have nd : base.Nodup := (List.nodup_finRange _).map b (fun _ _ sep e => sep (hb e))
  have big : base.length=m+4 := by simp [base]
  obtain ⟨p,hp,q,hq,pq,epq,xs,nx,lx,fresh⟩ := pickEdge c r hit base nd (by omega)
  obtain ⟨s,hs,t,ht,st,est,ys,ny,ly,new⟩ := pickEdge c r hit xs nx (by omega)
  obtain ⟨u,hu,v,hv,uv,euv,_⟩ := pickEdge c r hit ys ny (by omega)
  have su := new u hu
  have sv := new v hv
  have fs := fresh s hs
  have ft := fresh t ht
  have fu := fresh u su.2.2
  have fv := fresh v sv.2.2
  have away (i : Fin 3) (z) (hz : z ∈ base) : a i ≠ z := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    exact disj i j
  have e (i : Fin 3) (z) (hz : z ∈ base) : c.edge (a i) z = r := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hz
    exact cross i j
  let vertices := [a 0,p,q,a 1,s,t,a 2,u,v]
  have different : vertices.Nodup := by
    have aa : ∀ i j, i≠j → a i≠a j := fun _ _ sep h => sep (ha h)
    simp only [vertices,List.nodup_cons,List.nodup_nil,List.mem_cons,
      List.mem_nil_iff,not_or,or_false,and_true]
    have ab : a 0≠a 1 := aa _ _ (by decide)
    have ac : a 0≠a 2 := aa _ _ (by decide)
    have bc : a 1≠a 2 := aa _ _ (by decide)
    grind
  let point (i : Fin 9) := vertices[i.val]'i.isLt
  refine ⟨r,point,fun {_ _} h => Fin.ext (different.eq_of_getElem_eq _ _ h),?_⟩
  intro i
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact e 0 p hp
  · exact epq
  · exact (c.symm _ _).trans (e 1 q hq)
  · exact e 1 s fs.2.2
  · exact est
  · exact (c.symm _ _).trans (e 2 t ft.2.2)
  · exact e 2 u fu.2.2
  · exact euv
  · exact (c.symm _ _).trans (e 0 v fv.2.2)

/-- Any monochromatic K₃,₂₀ in K₃₃ forces a monochromatic nine-cycle. -/
theorem hasMonoC9_of_three_twenty (c : Coloring 33) (r : Fin 3)
    (a : Fin 3 → Fin 33) (b : Fin 20 → Fin 33)
    (ha : ∀ ⦃i j⦄, a i=a j → i=j) (hb : ∀ ⦃i j⦄, b i=b j → i=j)
    (disj : ∀ i j, a i≠b j) (red : ∀ i j, c.edge (a i) (b j)=r) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  apply free
  apply hasMonoC9_of_three_matching (m := 16) c r a b (@ha) (@hb) disj red
  intro v vi
  apply Classical.byContradiction; intro none
  exact free (hasMonoC9_of_independent16 twoColorOctets16 c v (@vi) r
    (fun i j sep e => none ⟨i,j,sep,e⟩))

end Ramsey556.BicliqueObstruction
