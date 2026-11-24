import Wall133.ShortGirthOptions
import Wall133.FiveCycle

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def seen (a b : Finset (Fin 3)) (s : Finset (Fin 3)) := a=s ∨ b=s
private instance (a b s : Finset (Fin 3)) : Decidable (seen a b s) := by unfold seen; infer_instance

private theorem three_site_table : ∀ a b : Finset (Fin 3), 0 < a.card → 0 < b.card → Disjoint a b →
    seen a b {0} ∨ (seen a b {1} ∧ seen a b {2}) ∨ (seen a b {1} ∧ seen a b {0,2}) ∨
      (seen a b {0,1} ∧ seen a b {2}) := by unfold seen; decide

private def privateAt (P : Chain G 4) (x : V) (j : ℕ) :=
  ∃ b, G.Adj x b ∧ Off P b (· = j)
private def sharedAt (P : Chain G 4) (x : V) (j : ℕ) :=
  ∃ b, G.Adj x b ∧ G.Adj (P.vertex 2) b ∧ G.Adj (P.vertex j) b

private theorem stalled_three_sites (P : Chain G 4) (h4 : NoFourCycle G)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (hd : 3 ≤ G.indepNeighborsCard x ∨ 4 ≤ G.degree x) (short : ¬7≤G.path) :
    (privateAt P x 3 ∧ privateAt P x 4) ∨ (privateAt P x 3 ∧ sharedAt P x 4) ∨
      (sharedAt P x 3 ∧ privateAt P x 4) := by
  classical
  let R := grow P x hx
  obtain ⟨A⟩ := exists_contact_options R (by decide) h4 hd
  have sz := A.size
  obtain ⟨b,c,hb,hc,bc⟩ := Finset.one_lt_card_iff.mp (by omega : 1<A.points.card)
  let supp (z : V) := (Finset.univ : Finset (Fin 3)).filter (fun j => G.Adj z (P.vertex (j.val+2)))
  have mem {z : V} {j : Fin 3} : j∈supp z ↔ G.Adj z (P.vertex (j.val+2)) := by simp [supp]
  have ne {z} (hz : z∈A.points) : (supp z).Nonempty := by
    by_contra! empty
    have good : Good R z := by
      refine ⟨A.adj _ hz,A.fresh _ hz,?_⟩
      rintro (_|i) hi ip ha
      · contradiction
      · have lo := A.lower _ hz (i+1) hi ip ha
        let j : Fin 3 := ⟨i-2,by omega⟩
        have eq : j.val+2=i := by dsimp [j]; omega
        have hm : j∈supp z := mem.mpr (eq ▸ ha)
        simp [empty] at hm
    exact short (grow R z good).length_le
  have disj : Disjoint (supp b) (supp c) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact bc (h4 (hx.2.1 (j.val+2) (by have := j.isLt; omega))
      (A.adj b hb) (mem.mp hj).symm (A.adj c hc) (mem.mp hk).symm)
  have realize {s : Finset (Fin 3)} (hs : seen (supp b) (supp c) s) :
      ∃ z ∈ A.points, supp z=s := hs.elim (fun e => ⟨b,hb,e⟩) (fun e => ⟨c,hc,e⟩)
  have sing (j : Fin 3) (hs : seen (supp b) (supp c) {j}) : privateAt P x (j.val+2) := by
    obtain ⟨z,hz,eq⟩ := realize hs
    refine ⟨z,A.adj _ hz,⟨fun i hi => A.fresh _ hz (i+1) (by omega),?_⟩⟩
    intro i hi
    constructor
    · intro ha
      have lo := A.lower _ hz (i+1) (by omega) (by omega) ha
      let k : Fin 3 := ⟨i-2,by omega⟩
      have ke : k.val+2=i := by dsimp [k]; omega
      have hk : k∈supp z := mem.mpr (ke ▸ ha)
      rw [eq,Finset.mem_singleton] at hk
      exact ke.symm.trans (congrArg (fun v : Fin 3 => v.val+2) hk)
    · rintro rfl
      exact mem.mp (by rw [eq]; simp)
  have pair (j : Fin 3) (hs : seen (supp b) (supp c) {0,j}) : sharedAt P x (j.val+2) := by
    obtain ⟨z,hz,eq⟩ := realize hs
    exact ⟨z,A.adj _ hz,(mem.mp (show (0:Fin 3)∈supp z by rw [eq]; simp)).symm,
      (mem.mp (show j∈supp z by rw [eq]; simp)).symm⟩
  rcases three_site_table _ _ (Finset.card_pos.mpr (ne hb)) (Finset.card_pos.mpr (ne hc)) disj with h|⟨h,j⟩|⟨h,j⟩|⟨h,j⟩
  · obtain ⟨z,hz,off⟩ := sing 0 h
    exact (short (independent_end_reroute P (by decide) h4 hx hy hxy nxy hz off.fresh off.contact)).elim
  · exact Or.inl ⟨sing 1 h,sing 2 j⟩
  · exact Or.inr (Or.inl ⟨sing 1 h,pair 2 j⟩)
  · exact Or.inr (Or.inr ⟨pair 1 h,sing 2 j⟩)

omit [DecidableRel G.Adj] in
private theorem path_of_two_private (P : Chain G 4) (h4 : NoFourCycle G)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (p3 : privateAt P x 3) (p4 : privateAt P y 4) : 7 ≤ G.path := by
  obtain ⟨b,hxb,hb⟩ := p3
  obtain ⟨c,hyc,hc⟩ := p4
  have ax := offGood hx
  have ay := offGood hy
  have hby : ¬G.Adj y b := fun hyb => hb.fresh 0 (by decide) (h4 hxy hxb hyb hx.1.symm hy.1.symm)
  have hcx : ¬G.Adj x c := fun hxc => hc.fresh 0 (by decide) (h4 hxy hxc hyc hx.1.symm hy.1.symm)
  have hbc : ¬G.Adj b c := fun h => hc.fresh 3 (by decide) (h4 (hb.fresh 4 (by decide)) h
    ((hc.contact 4 (by decide)).2 rfl).symm ((hb.contact 3 (by decide)).2 rfl)
    ((P.edges (by decide : 4≤4) (by decide : 3≤4)).2 (Or.inr rfl)))
  let f : Fin 7 → V := ![P.vertex 2,P.vertex 3,b,x,P.vertex 0,y,c]
  have edges (i j : Fin 7) : G.Adj (f i) (f j) ↔ i.val+1=j.val ∨ j.val+1=i.val := by
    fin_cases i <;> fin_cases j <;> dsimp [f]
    all_goals first
      | rw [P.edges (by decide) (by decide)] <;> decide
      | rw [hb.contact _ (by decide)] <;> decide
      | rw [hc.contact _ (by decide)] <;> decide
      | rw [ax.contact _ (by decide)] <;> decide
      | rw [ay.contact _ (by decide)] <;> decide
      | rw [G.adj_comm, hb.contact _ (by decide)] <;> decide
      | rw [G.adj_comm, hc.contact _ (by decide)] <;> decide
      | rw [G.adj_comm, ax.contact _ (by decide)] <;> decide
      | rw [G.adj_comm, ay.contact _ (by decide)] <;> decide
      | simp only [SimpleGraph.irrefl,hxb,hxb.symm,hyc,hyc.symm,hby,mt Adj.symm hby,hcx,mt Adj.symm hcx,
          hbc,mt Adj.symm hbc,nxy,mt Adj.symm nxy,true_iff,false_iff]; decide
  apply path_bound_of_indices f _ edges
  have twins : ∀ a b : Fin 7, (∀ k : Fin 7,(a.val+1=k.val ∨ k.val+1=a.val) ↔
      (b.val+1=k.val ∨ k.val+1=b.val)) → a=b := by decide
  intro i j eq
  apply twins i j
  intro k
  exact (edges i k).symm.trans ((congrArg (fun z => G.Adj z (f k)) eq).to_iff.trans (edges j k))

/-- Two clean independent extensions of a five-vertex path each having
three independent neighbors or degree four force a seven-vertex induced path. -/
theorem seven_of_two_low_rows (P : Chain G 4) (h4 : NoFourCycle G)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (hdx : 3≤G.indepNeighborsCard x ∨ 4≤G.degree x)
    (hdy : 3≤G.indepNeighborsCard y ∨ 4≤G.degree y) : 7≤G.path := by
  by_contra short
  have X := stalled_three_sites P h4 hx hy hxy nxy hdx short
  have Y := stalled_three_sites P h4 hy hx hxy.symm (fun h => nxy h.symm) hdy short
  have impossible (i : ℕ) (hi : i≤4) (hi2 : i≠2) (w : sharedAt P x i) (z : sharedAt P y i) : False := by
    obtain ⟨b,xb,pb,ib⟩ := w
    obtain ⟨c,yc,pc,ic⟩ := z
    have ne : P.vertex 2 ≠ P.vertex i := fun e => hi2 (P.inj (by decide) hi e).symm
    have bc := h4 ne pb ib pc ic
    have be := h4 hxy xb (bc ▸ yc) hx.1.symm hy.1.symm
    rw [be] at pb
    have := (P.edges (by decide : 2≤4) (by decide : 0≤4)).1 pb
    omega
  have xp := path_of_two_private P h4 hx hy hxy nxy
  have yp := path_of_two_private P h4 hy hx hxy.symm (fun h => nxy h.symm)
  rcases X with ⟨xa,xb⟩|⟨xa,xb⟩|⟨xa,xb⟩ <;> rcases Y with ⟨ya,yb⟩|⟨ya,yb⟩|⟨ya,yb⟩
  all_goals first | exact short (xp xa yb) | exact short (yp ya xb) |
    exact impossible 3 (by decide) (by decide) xa ya | exact impossible 4 (by decide) (by decide) xb yb

end Wall133
