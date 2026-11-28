import Ramsey556.TwoVertexFrame

namespace Ramsey556

theorem noIndependent17_of_free {c : Coloring 33} (classify : TwoColorOctets16)
    (free : ¬ HasMonoC9 c) : NoIndependent17 c := by
  intro v inj
  apply Classical.byContradiction
  intro h
  have absent : ∀ i j, i ≠ j → (c.induce v).edge i j ≠ 0 :=
    fun i j ne e => h ⟨i, j, ne, e⟩
  exact free (HasMonoC9.of_induce (@inj) (twoColor17_of_octets classify _ absent))

/-- Two independent lists containing at least 17 different vertices between
them must have a red edge from one list to the other. -/
private theorem red_between_lists {c : Coloring 33} (ind : NoIndependent17 c)
    (xs ys : List (Fin 33)) (size : 17 ≤ xs.length + ys.length)
    (nx : xs.Nodup) (ny : ys.Nodup) (disj : ∀ a ∈ xs, a ∉ ys)
    (ix : ∀ a ∈ xs, ∀ b ∈ xs, a ≠ b → c.edge a b ≠ 0)
    (iy : ∀ a ∈ ys, ∀ b ∈ ys, a ≠ b → c.edge a b ≠ 0) :
    ∃ a ∈ xs, ∃ b ∈ ys, c.edge a b = 0 := by
  let vs := xs ++ ys
  have nd : vs.Nodup := by
    apply List.pairwise_append.mpr
    refine ⟨nx, ny, ?_⟩
    exact fun a ha b hb eq => disj a ha (eq ▸ hb)
  have len : 17 ≤ vs.length := by simpa [vs] using size
  let v (i : Fin 17) := vs[i.val]'(by omega)
  have inj : ∀ ⦃i j⦄, v i = v j → i = j :=
    fun {_ _} e => Fin.ext (nd.eq_of_getElem_eq _ _ e)
  obtain ⟨i,j,ne,e⟩ := ind v inj
  have apart : v i ≠ v j := fun eq => ne (inj eq)
  have mem (i : Fin 17) : v i ∈ xs ∨ v i ∈ ys :=
    List.mem_append.mp (List.getElem_mem (l := vs) (n := i.val) _)
  rcases mem i with hi | hi <;> rcases mem j with hj | hj
  · exact (ix _ hi _ hj apart e).elim
  · exact ⟨_,hi,_,hj,e⟩
  · exact ⟨_,hj,_,hi,(c.symm _ _).trans e⟩
  · exact (iy _ hi _ hj apart e).elim

/-- In the small exterior class each of u and v sees all but one anchor
in its octet. Use the absence of a red-independent 17-set twice, removing
the ends of the first link before choosing the second. -/
theorem two_links_of_large_type {c : Coloring 33} (S : SupportedOctets c)
    (ind : NoIndependent17 c) (big small : Fin 2) (_hbs : big ≠ small)
    (large : 13 ≤ (S.members big).length)
    (inner : ∀ i j, i ≠ j → S.tag i = big → S.tag j = big → c.edge (S.outer i) (S.outer j) ≠ 0)
    (u v : Fin 17) (hu : S.tag u = small) (hv : S.tag v = small) :
    ∃ (p q : Fin 17) (a b : Fin 8), p ≠ q ∧ a ≠ b ∧ S.tag p = big ∧ S.tag q = big ∧
      c.edge (S.outer p) (S.anchor small a) = 0 ∧ c.edge (S.outer q) (S.anchor small b) = 0 ∧
      c.edge (S.outer u) (S.anchor small a) = 0 ∧ c.edge (S.outer v) (S.anchor small b) = 0 := by
  obtain ⟨badU,goodU⟩ := S.supports u
  obtain ⟨badV,goodV⟩ := S.supports v
  rw [hu] at goodU
  rw [hv] at goodV
  let xs := S.members big
  let ys := (List.finRange 8).filter (fun i => i != badU && i != badV)
  have enough : ∀ k l : Fin 8,
      6 ≤ ((List.finRange 8).filter (fun i => i != k && i != l)).length := by decide
  have ny : ys.Nodup := (List.nodup_finRange 8).filter _
  have nx : xs.Nodup := (List.nodup_finRange 17).filter _
  have tag {i : Fin 17} (h : i ∈ xs) : S.tag i = big :=
    beq_iff_eq.mp (List.mem_filter.mp h).2
  have link (us : List (Fin 17)) (vs : List (Fin 8)) (size : 17 ≤ us.length + vs.length)
      (nu : us.Nodup) (nv : vs.Nodup) (sub : us ⊆ xs) :
      ∃ p ∈ us, ∃ a ∈ vs, c.edge (S.outer p) (S.anchor small a) = 0 := by
    have found := red_between_lists ind (us.map S.outer) (vs.map (S.anchor small)) (by simpa using size)
      (nu.map _ (fun _ _ ne e => ne (S.outerInj e)))
      (nv.map _ (fun _ _ ne e => ne (S.anchorInj e).2))
    have d : ∀ a ∈ us.map S.outer, a ∉ vs.map (S.anchor small) := by
      rintro _ h h'
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp h
      obtain ⟨j, _, eq⟩ := List.mem_map.mp h'
      exact S.disjoint small j i eq
    have ex := found d (by
      rintro _ ha _ hb ne
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      exact inner _ _ (fun eq => ne (congrArg S.outer eq)) (tag (sub hi)) (tag (sub hj))) (by
      rintro _ ha _ hb ne
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      exact S.independent _ _ _ _ (fun eq => ne (congrArg (S.anchor small) (congrArg Prod.snd eq))))
    obtain ⟨a,ha,b,hb,e⟩ := ex
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hb
    exact ⟨p,hp,i,hi,e⟩
  have xlen : 13 ≤ xs.length := large
  have ylen : 6 ≤ ys.length := enough _ _
  obtain ⟨p,hp,a,ha,e₁⟩ := link xs ys (by omega) nx ny (fun {_} h => h)
  have len : 17 ≤ (xs.erase p).length + (ys.erase a).length := by
    rw [List.length_erase_of_mem hp, List.length_erase_of_mem ha]; omega
  obtain ⟨q,hq,b,hb,e₂⟩ := link _ _ len (nx.erase _) (ny.erase _) List.erase_subset
  obtain ⟨qp,hq'⟩ := nx.mem_erase_iff.mp hq
  obtain ⟨ba,hb'⟩ := ny.mem_erase_iff.mp hb
  have valid {i} (him : i ∈ ys) : i ≠ badU ∧ i ≠ badV := by
    simpa [ys] using him
  exact ⟨p,q,a,b,qp.symm,ba.symm,tag hp,tag hq',e₁,e₂,goodU a (valid ha).1,goodV b (valid hb').2⟩

end Ramsey556
