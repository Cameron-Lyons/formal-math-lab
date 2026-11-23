import Ramsey556.FifteenPaths
import Ramsey556.Split17

namespace Ramsey556.Biclique13

/-- Seven consecutive indices, starting at `a` in the direction away from
the forbidden index when it lies among the next six clockwise vertices. -/
private def arc (a blocked : Fin 13) (i : Fin 7) : Fin 13 :=
  let j : Fin 13 := ⟨i.val,by omega⟩
  if 0 < (blocked-a).val ∧ (blocked-a).val ≤ 6 then a-j else a+j

private theorem arc_spec : ∀ a b : Fin 13, arc a b 0 = a ∧
    (∀ i j, arc a b i = arc a b j → i = j) ∧ (a≠b → ∀ i, arc a b i ≠ b) := by decide +kernel

private theorem incompatible (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c)
    (A B : Fin 13 → Fin 33) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (ab : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j) = r)
    (x : Fin 33) (a b skipA skipB : Fin 13)
    (ax : ∀ i, A (arc a skipA i) ≠ x) (bx : ∀ i, B (arc b skipB i) ≠ x)
    (ea : c.edge x (A a)=r) (eb : c.edge x (B b)=r) : False := by
  obtain ⟨a0,ia,_⟩ := arc_spec a skipA
  obtain ⟨b0,ib,_⟩ := arc_spec b skipB
  exact Fifteen.biclique_spokes c r (fun i => A (arc a skipA i)) (fun j => B (arc b skipB j)) x
    (fun {_ _} h => ia _ _ (ai h)) (fun {_ _} h => ib _ _ (bi h)) (fun _ _ => ab _ _) ax bx
    (fun _ _ => cross _ _) free (a:=0) (b:=0) (by simpa only [a0] using ea) (by simpa only [b0] using eb)

private theorem independent (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c)
    (A B : Fin 13 → Fin 33) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (ab : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j) = r) :
    ∀ i j, i≠j → c.edge (A i) (A j) ≠ r := fun i j ne edge =>
  incompatible c r free A B ai bi ab cross (A i) j 0 i 0
    (fun _ e => (arc_spec j i).2.2 ne.symm _ (ai e)) (fun _ e => ab _ _ e.symm) edge (cross i 0)

private theorem make_split (c : Coloring 33) (r : Fin 3)
    (shore : Fin 13 → Fin 33) (out : Fin 4 → Fin 33)
    (si : ∀ ⦃i j⦄, shore i=shore j → i=j) (oi : ∀ ⦃i j⦄, out i=out j → i=j)
    (sep : ∀ i j, shore i ≠ out j) (inside : ∀ i j, i≠j → c.edge (shore i) (shore j) ≠ r)
    (outside : ∀ i j, c.edge (out j) (shore i) ≠ r) :
    ∃ v : Fin 17 → Fin 33, (∀ ⦃i j⦄, v i=v j → i=j) ∧ ∀ i j, i≠j →
      (i.val < 13 ∨ j.val < 13) → c.edge (v i) (v j) ≠ r := by
  let v (i : Fin 17) : Fin 33 := Fin.addCases (m:=13) (n:=4) (motive:=fun _ => Fin 33) shore out i
  refine ⟨v,?_,?_⟩
  · intro i j h
    induction i using Fin.addCases (m:=13) (n:=4) <;> induction j using Fin.addCases (m:=13) (n:=4) <;>
      simp only [v,Fin.addCases_left,Fin.addCases_right] at h
    · exact congrArg _ (si h)
    · exact (sep _ _ h).elim
    · exact (sep _ _ h.symm).elim
    · exact congrArg _ (oi h)
  · intro i j ne prop e
    induction i using Fin.addCases (m:=13) (n:=4) <;> induction j using Fin.addCases (m:=13) (n:=4) <;>
      simp only [v,Fin.addCases_left,Fin.addCases_right] at e
    · exact inside _ _ (fun h => ne (congrArg _ h)) e
    · exact outside _ _ ((c.symm _ _).trans e)
    · exact outside _ _ e
    · simp only [Fin.val_natAdd] at prop
      omega

/-- In a C₉-free coloring, a red K₁₃,₁₃ gives a shore and four exterior
vertices with no red edges incident with the shore in their induced K₁₇. -/
theorem absent_split (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c)
    (A B : Fin 13 → Fin 33) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (ab : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j) = r) :
    ∃ v : Fin 17 → Fin 33, (∀ ⦃i j⦄, v i=v j → i=j) ∧ ∀ i j, i≠j →
      (i.val < 13 ∨ j.val < 13) → c.edge (v i) (v j) ≠ r := by
  classical
  let both (i : Fin 26) : Fin 33 := Fin.addCases (m:=13) (n:=13) (motive:=fun _ => Fin 33) A B i
  obtain ⟨w,wi,away⟩ := Fifteen.exterior (a:=26) (b:=7) (by decide) both
  have awayA (i j) : A i ≠ w j := by simpa [both] using away (Fin.castAdd 13 i) j
  have awayB (i j) : B i ≠ w j := by simpa only [both, Fin.addCases_right] using away (Fin.natAdd 13 i) j
  let tag (i : Fin 7) := decide (∃ a, c.edge (w i) (A a) = r)
  let cell (b : Bool) := (List.finRange 7).filter (fun i => tag i == b)
  have total : 7 = (cell true).length + (cell false).length := by
    simpa [cell, List.countP_eq_length_filter] using List.length_eq_countP_add_countP tag (l:=List.finRange 7)
  obtain ⟨pick,large⟩ : ∃ b, 4 ≤ (cell b).length := by
    by_cases h : 4 ≤ (cell true).length
    · exact ⟨true,h⟩
    · exact ⟨false,by omega⟩
  let shore (i : Fin 13) := if pick then B i else A i
  let sel (j : Fin 4) := (cell pick)[j.val]'(by omega)
  let out (j : Fin 4) := w (sel j)
  have same (j : Fin 4) : tag (sel j) = pick := by
    have mem : sel j ∈ cell pick := List.getElem_mem ..
    exact beq_iff_eq.mp (List.mem_filter.mp mem).2
  have si : ∀ ⦃i j⦄, shore i=shore j → i=j := by
    cases pick <;> first | exact @ai | exact @bi
  have oi : ∀ ⦃i j⦄, out i=out j → i=j := by
    intro i j h
    have nd : (cell pick).Nodup := (List.nodup_finRange _).filter _
    exact Fin.ext (nd.eq_of_getElem_eq _ _ (wi h))
  have sep (i j) : shore i ≠ out j := by
    cases pick <;> first | exact awayA _ _ | exact awayB _ _
  have inside (i j) (ne : i≠j) : c.edge (shore i) (shore j) ≠ r := by
    cases pick
    · exact independent c r free A B ai bi ab cross i j ne
    · exact independent c r free B A bi ai (fun u v => (ab _ _).symm)
        (fun u v => (c.symm _ _).trans (cross _ _)) i j ne
  have outside (i j) : c.edge (out j) (shore i) ≠ r := by
    have bit := same j
    cases pick
    · have h : ¬ ∃ a, c.edge (w (sel j)) (A a) = r := of_decide_eq_false bit
      exact fun e => h ⟨i,e⟩
    · obtain ⟨a,ea⟩ := of_decide_eq_true bit
      exact incompatible c r free A B ai bi ab cross (w (sel j)) a i a i
        (fun _ => awayA _ _) (fun _ => awayB _ _) ea
  exact make_split c r shore out (@si) (@oi) sep inside outside


/-- Exterior vertices joined to a given 13-set by an edge of color r. -/
def dominated (c : Coloring 33) (r : Fin 3) (v : Fin 13 → Fin 33) : List (Fin 33) :=
  (List.finRange 33).filter (fun x => !((List.finRange 13).any (fun a => v a == x)) &&
    (List.finRange 13).any (fun a => c.edge x (v a) == r))

private theorem domination_of_no_split (c : Coloring 33) (r : Fin 3)
    (noSplit : ¬ ∃ w : Fin 17 → Fin 33, (∀ ⦃i j⦄, w i=w j → i=j) ∧ ∀ i j, i≠j →
      (i.val < 13 ∨ j.val < 13) → c.edge (w i) (w j) ≠ r)
    (v : Fin 13 → Fin 33) (vi : ∀ ⦃i j⦄, v i=v j → i=j)
    (ind : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : 17 ≤ (dominated c r v).length := by
  classical
  obtain ⟨w,wi,away⟩ := Fifteen.exterior (a:=13) (b:=20) (by decide) v
  let p (i : Fin 20) := decide (∃ a, c.edge (w i) (v a) = r)
  let hits := (List.finRange 20).filter p
  let misses := (List.finRange 20).filter (fun i => !p i)
  have part : 20 = hits.length + misses.length := by
    simpa [hits,misses,List.countP_eq_length_filter] using List.length_eq_countP_add_countP p (l:=List.finRange 20)
  have room : misses.length < 4 := by
    apply Classical.byContradiction
    intro h
    let f (i : Fin 4) := misses[i.val]'(by omega)
    have nd : misses.Nodup := (List.nodup_finRange _).filter _
    apply noSplit (make_split c r v (fun i => w (f i)) (@vi)
      (fun {_ _} e => Fin.ext (nd.eq_of_getElem_eq _ _ (wi e))) (fun _ _ => away _ _) ind ?_)
    intro a j edge
    have mem : f j ∈ misses := List.getElem_mem ..
    have empty : ¬ ∃ a, c.edge (w (f j)) (v a) = r := by simpa [misses,p] using mem
    exact empty ⟨a,edge⟩
  have nd : (hits.map w).Nodup := ((List.nodup_finRange 20).filter _).map w (fun _ _ ne e => ne (wi e))
  have sub : hits.map w ⊆ dominated c r v := by
    intro x mem
    obtain ⟨i,h,rfl⟩ := List.mem_map.mp mem
    obtain ⟨a,edge⟩ := of_decide_eq_true (List.mem_filter.mp h).2
    simpa [dominated,List.any_eq_true, List.any_eq_false,away] using
      (show (∀ a, v a ≠ w i) ∧ ∃ a, c.edge (w i) (v a) = r from ⟨fun a => away a i, a,edge⟩)
  have le := nd.length_le_of_subset sub
  rw [List.length_map] at le
  omega

private theorem no_split (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c) :
    ¬ ∃ w : Fin 17 → Fin 33, (∀ ⦃i j⦄, w i=w j → i=j) ∧ ∀ i j, i≠j →
      (i.val < 13 ∨ j.val < 13) → c.edge (w i) (w j) ≠ r := by
  rintro ⟨w,wi,absent⟩
  have ne : ∀ k : Fin 3, k+1 ≠ k+2 := by decide
  have other : ∀ k x : Fin 3, x≠k → x=k+1 ∨ x=k+2 := by decide
  exact free (Split17.hasMonoC9 c (r+1) (r+2) (ne r) w (@wi)
    (fun i j ij inc => other r _ (absent i j ij inc)))

/-- A color-independent shore of thirteen and four exterior vertices
missing that shore in the same color force a monochromatic nine-cycle. -/
theorem split_forces (c : Coloring 33) (r : Fin 3) (shore : Fin 13 → Fin 33) (out : Fin 4 → Fin 33)
    (si : ∀ ⦃i j⦄, shore i=shore j → i=j) (oi : ∀ ⦃i j⦄, out i=out j → i=j)
    (sep : ∀ i j, shore i ≠ out j) (inside : ∀ i j, i≠j → c.edge (shore i) (shore j) ≠ r)
    (outside : ∀ i j, c.edge (out j) (shore i) ≠ r) : HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  exact no_split c r free (make_split c r shore out si oi sep inside outside)

/-- A single monochromatic K₁₃,₁₃ in K₃₃ forces a monochromatic nine-cycle. -/
theorem forces_cycle (c : Coloring 33) (r : Fin 3)
    (A B : Fin 13 → Fin 33) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (bi : ∀ ⦃i j⦄, B i=B j → i=j)
    (ab : ∀ i j, A i ≠ B j) (cross : ∀ i j, c.edge (A i) (B j) = r) : HasMonoC9 c :=
  Classical.byContradiction (fun free => no_split c r free (absent_split c r free A B ai bi ab cross))

/-- Every color-independent 13-set in a counterexample dominates at least
seventeen of the twenty outside vertices in that color. -/
theorem independent13_dominates (c : Coloring 33) (r : Fin 3) (free : ¬ HasMonoC9 c)
    (v : Fin 13 → Fin 33) (vi : ∀ ⦃i j⦄, v i=v j → i=j)
    (ind : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : 17 ≤ (dominated c r v).length :=
  domination_of_no_split c r (no_split c r free) v vi ind

end Ramsey556.Biclique13
