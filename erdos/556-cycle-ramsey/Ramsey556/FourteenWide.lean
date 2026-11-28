import Ramsey556.Fourteen
import Ramsey556.FifteenPaths
import Ramsey556.AnchorClosure

namespace Ramsey556.Fourteen

private def wideA (i : Fin 8) : Fin 14 := ⟨i.val,by omega⟩
/-- The six-clique in the unbalanced template. -/
def wideB (i : Fin 6) : Fin 14 := ⟨i.val+8,by omega⟩
private def cleanA (i : Fin 7) := wideA i.castSucc

/-- These exterior vertices miss the cut color throughout the six-clique
and send the clique color to at least two of its vertices. -/
def RichOnSix (c : Coloring 33) (anchor : Fin 14 → Fin 33) (green blue : Fin 3) (x : Fin 33) : Prop :=
  (∀ j, c.edge x (anchor (wideB j)) ≠ blue) ∧
  ∃ a b : Fin 6, a ≠ b ∧ c.edge x (anchor (wideB a)) = green ∧ c.edge x (anchor (wideB b)) = green

private theorem supported_others (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (anchor : Fin 14 → Fin 33) (inj : Function.Injective anchor)
    (ind : ∀ i j, i ≠ j → c.edge (anchor i) (anchor j) ≠ 0)
    (t : Fin 8) (green blue : Fin 3) (g0 : green ≠ 0) (b0 : blue ≠ 0) (gb : green ≠ blue)
    (edges : ∀ i j, i ≠ j →
      c.edge (anchor i) (anchor j) = if template14 true t i j then green else blue)
    (outer : Fin 17 → Fin 33) (oi : Function.Injective outer)
    (away : ∀ a i, anchor a ≠ outer i)
    (ordinary : ∀ i, ¬ RichOnSix c anchor green blue (outer i)) : Nonempty (AnchorSupport c 14) := by
  let A (i : Fin 8) := anchor (wideA i)
  let B (i : Fin 6) := anchor (wideB i)
  let C (i : Fin 7) := anchor (cleanA i)
  have ai : Function.Injective wideA := by unfold Function.Injective; decide
  have bi : Function.Injective wideB := by unfold Function.Injective; decide
  have ci : Function.Injective cleanA := by unfold Function.Injective; decide
  have sep : ∀ i j, cleanA i ≠ wideB j := by decide
  have clique (i j : Fin 8) (ne : i ≠ j) : c.edge (A i) (A j) = green := by
    simpa [A, template14, wideA, i.isLt, j.isLt] using edges (wideA i) (wideA j) (ai.ne ne)
  have cross (i j) : c.edge (C i) (B j) = blue := by
    have shape : template14 true t (cleanA i) (wideB j) = false := by
      simp [template14, cleanA, wideA, wideB]; omega
    simpa [shape] using edges (cleanA i) (wideB j) (sep i j)
  have color (z : Fin 3) (hg : z ≠ green) (hb : z ≠ blue) : z = 0 := by omega
  let touches (i : Fin 17) := ∃ j, c.edge (outer i) (B j) = blue
  let tag (i : Fin 17) : Fin 2 := if touches i then 0 else 1
  have fewA (i : Fin 17) : Fifteen.AtMostOne (fun j => c.edge (outer i) (C j) = green) := by
    apply Fifteen.one_of_unique
    intro a b ha hb
    exact Fin.castSucc_inj.mp (clique_spokes_unique c green A (outer i) (inj.comp ai)
      (fun _ => away _ _) clique free ha hb)
  have fewB (i : Fin 17) (h : ¬ touches i) :
      ∃ u, ∀ j, c.edge (outer i) (B j) = green → j = u := by
    apply Fifteen.single_exception
    intro u v hu hv
    exact Classical.byContradiction (fun ne => ordinary i ⟨fun b hb => h ⟨b,hb⟩,u,v,ne,hu,hv⟩)
  have miss (i : Fin 17) (h : touches i) (a : Fin 7) : c.edge (outer i) (C a) ≠ blue := by
    obtain ⟨b,hb⟩ := h
    exact fun ha => Fifteen.biclique_spokes_of_sizes c blue C B (outer i) (by decide) (by decide)
      (inj.comp ci) (inj.comp bi) (fun u v eq => sep u v (inj eq))
      (fun _ => away _ _) (fun _ => away _ _) cross free ha hb
  refine ⟨⟨anchor,outer,tag,@inj,@oi,away,ind,?_⟩⟩
  intro i j same
  have agree : touches i ↔ touches j := by
    by_cases a : touches i <;> by_cases b : touches j <;> simp_all [tag]
  by_cases hi : touches i
  · have hj := agree.mp hi
    apply Fifteen.four_common_on_seven _ _ cleanA ci color
      (Fifteen.union_three (a:=0) (b:=0) (Or.inl (fewA i)) (Or.inl (fewA j)))
    exact fun z => ⟨miss i hi z,miss j hj z⟩
  · have hj := mt agree.mpr hi
    obtain ⟨u,hu⟩ := fewB i hi
    obtain ⟨v,hv⟩ := fewB j hj
    have bound := Fifteen.count_outside
      (fun a => c.edge (outer i) (anchor a) == 0 && c.edge (outer j) (anchor a) == 0)
      wideB bi [u,v] (by
        intro z keep
        have ⟨zu,zv⟩ : z ≠ u ∧ z ≠ v := by simpa using keep
        have ei := color _ (fun h => zu (hu z h)) (fun h => hi ⟨z,h⟩)
        have ej := color _ (fun h => zv (hv z h)) (fun h => hj ⟨z,h⟩)
        simpa only [Bool.and_eq_true, beq_iff_eq] using And.intro ei ej)
    simp only [List.length_cons,List.length_nil] at bound
    omega

/-- Every unbalanced template in a counterexample has three distinct exterior
vertices with the neighborhood restriction `RichOnSix`. -/
theorem wide_three_rich (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (anchor : Fin 14 → Fin 33) (inj : Function.Injective anchor)
    (ind : ∀ i j, i ≠ j → c.edge (anchor i) (anchor j) ≠ 0)
    (t : Fin 8) (green blue : Fin 3) (g0 : green ≠ 0) (b0 : blue ≠ 0) (gb : green ≠ blue)
    (edges : ∀ i j, i ≠ j →
      c.edge (anchor i) (anchor j) = if template14 true t i j then green else blue) :
    ∃ x : Fin 3 → Fin 33, (∀ ⦃i j⦄, x i = x j → i = j) ∧
      (∀ a i, anchor a ≠ x i) ∧ ∀ i, RichOnSix c anchor green blue (x i) := by
  classical
  obtain ⟨w,wi,away⟩ := outside_vertices (a:=14) (b:=19) (by decide) anchor
  let p (i : Fin 19) := decide (RichOnSix c anchor green blue (w i))
  let many := (List.finRange 19).filter p
  let few := (List.finRange 19).filter (fun i => !(p i))
  have partition : 19 = many.length + few.length := by
    simpa [many,few,List.countP_eq_length_filter] using List.length_eq_countP_add_countP p (l:=List.finRange 19)
  by_cases enough : 3 ≤ many.length
  · obtain ⟨select,si,rich⟩ := select_where p enough
    exact ⟨w ∘ select, wi.comp si, fun _ _ => away _ _, fun i => of_decide_eq_true (rich i)⟩
  · obtain ⟨select,si,plain⟩ := select_where (fun i => !p i) (m:=17) (by change 17 ≤ few.length; omega)
    have ordinary i : ¬ RichOnSix c anchor green blue (w (select i)) := by simpa [p] using plain i
    obtain ⟨S⟩ := supported_others c free anchor inj ind t green blue g0 b0 gb edges
      (w ∘ select) (wi.comp si) (fun _ _ => away _ _) ordinary
    exact (free (S.forces_cycle_of_size (by decide) twoColorOctets16)).elim

end Ramsey556.Fourteen
