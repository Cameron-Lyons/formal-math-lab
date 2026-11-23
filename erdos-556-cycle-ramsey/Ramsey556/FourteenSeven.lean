import Ramsey556.AnchorSupport
import Ramsey556.Fourteen
import Ramsey556.FifteenPaths
import Ramsey556.StarBiclique

namespace Ramsey556.Fourteen

private def left (i : Fin 7) : Fin 14 := ⟨i.val, by omega⟩
private def right (i : Fin 7) : Fin 14 := ⟨i.val+7, by omega⟩

/-- In the balanced template, omit one exterior vertex for each seven-clique.
On the side of a six-edge exceptional star, the star center itself rules out
two clique-colored spokes at any exterior vertex. -/
theorem support_seven_seven (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (anchor : Fin 14 → Fin 33) (inj : Function.Injective anchor)
    (ind : ∀ i j, i ≠ j → c.edge (anchor i) (anchor j) ≠ 0)
    (t : Fin 8) (ht : t.val ≤ 6) (green blue : Fin 3)
    (g0 : green ≠ 0) (b0 : blue ≠ 0) (gb : green ≠ blue)
    (edges : ∀ i j, i ≠ j →
      c.edge (anchor i) (anchor j) = if template14 false t i j then green else blue) :
    Nonempty (AnchorSupport c 14) := by
  let A (i : Fin 7) := anchor (left i)
  let B (i : Fin 7) := anchor (right i)
  have li : Function.Injective left := by unfold Function.Injective; decide
  have ri : Function.Injective right := by unfold Function.Injective; decide
  have lr : ∀ i j, left i ≠ right j := by decide
  have ai : Function.Injective A := inj.comp li
  have bi : Function.Injective B := inj.comp ri
  have sep (i j : Fin 7) : A i ≠ B j := inj.ne (lr i j)
  have color (x : Fin 3) (hg : x ≠ green) (hb : x ≠ blue) : x = 0 := by omega
  have cliqueA (i j : Fin 7) (ne : i ≠ j) : c.edge (A i) (A j) = green := by
    simpa [A, template14, left, i.isLt, j.isLt] using edges (left i) (left j) (li.ne ne)
  have cliqueB (i j : Fin 7) (ne : i ≠ j) : c.edge (B i) (B j) = green := by
    simpa +arith [B, template14, right] using edges (right i) (right j) (ri.ne ne)
  have cross (i j : Fin 7) (h : i ≠ 6 ∨ t.val ≤ j.val) : c.edge (A i) (B j) = blue := by
    have shape : template14 false t (left i) (right j) = false := by
      simp [template14, left, right, i.isLt]; omega
    simpa [shape] using edges (left i) (right j) (lr i j)
  have star (j : Fin 7) (less : j.val < t.val) : c.edge (A 6) (B j) = green := by
    have shape : template14 false t (left 6) (right j) = true := by
      simp [template14, left, right]; omega
    simpa only [shape, ↓reduceIte] using edges (left 6) (right j) (lr 6 j)
  obtain ⟨w,wi,away⟩ := outside_vertices (a:=14) (b:=19) (by decide) anchor
  obtain ⟨zB,pB,qB,sB⟩ := Fifteen.omit_one c green free B w bi wi (fun i j => away _ _) cliqueB
  let w' := w ∘ Fifteen.skip zB
  have w'Inj := wi.comp (Fifteen.skip_injective zB)
  obtain ⟨zA,pA,qA,sA⟩ := Fifteen.omit_one c green free A w' ai
    w'Inj (fun _ _ => away _ _) cliqueA
  let outer := w' ∘ Fifteen.skip zA
  have outerInj := w'Inj.comp (Fifteen.skip_injective zA)
  have outerAway (a j) : anchor a ≠ outer j := away _ _
  let touches (j : Fin 17) := ∃ i, c.edge (outer j) (A i) = blue
  let tag (j : Fin 17) : Fin 2 := if touches j then 1 else 0
  have blueSites (j : Fin 17) (has : touches j) {b : Fin 7} (hb : c.edge (outer j) (B b) = blue) :
      b = 6 ∧ t.val = 6 := by
    obtain ⟨a,ha⟩ := has
    have path (q : Fin 7) (qb : q ≠ b) (good : t.val ≤ q.val) : False :=
      StarBiclique.star_spokes_from c blue A B (outer j) ai bi sep
        (fun i => outerAway _ _) (fun i => outerAway _ _) 6 q
        (fun i j ne => cross i j (Or.inl ne)) qb (cross a q (Or.inr good)) free ha hb
    have b6 : b = 6 := Classical.byContradiction (fun h => path 6 (Ne.symm h) ht)
    refine ⟨b6,?_⟩
    apply Classical.byContradiction
    intro ne
    exact path 5 (b6 ▸ (by decide : (5 : Fin 7) ≠ 6)) (by change t.val ≤ 5; omega)
  have fewB (j : Fin 17) (size : t.val = 6) :
      Fifteen.AtMostOne (fun i => c.edge (outer j) (B i) = green) := by
    apply Fifteen.one_of_unique
    intro p q hp hq
    apply Classical.byContradiction
    intro pq
    obtain ⟨a,b,ab,ha,hb,pa,pb⟩ := (by decide : ∀ p : Fin 7,
       ∃ a b : Fin 7, a ≠ b ∧ a.val < 3 ∧ b.val < 3 ∧ p ≠ a ∧ p ≠ b) p
    have bad := Fifteen.clique_seven_pairs c green B (A 6) (outer j) bi (outerAway _ _)
      (fun i => (sep _ _).symm) (fun i => outerAway _ _) cliqueB free ab pq
      (star a (by omega)) (star b (by omega)) hp hq
    exact bad.elim pa pb
  refine ⟨⟨anchor,outer,tag,@inj,outerInj,
    outerAway,ind,?_⟩⟩
  intro i j same
  have agree : touches i ↔ touches j := by
    by_cases a : touches i <;> by_cases b : touches j <;> simp_all [tag]
  by_cases hi : touches i
  · have hj := agree.mp hi
    by_cases size : t.val = 6
    · obtain ⟨u,hu⟩ := fewB i size
      obtain ⟨v,hv⟩ := fewB j size
      apply Fifteen.four_in_core _ right ri (u:=u) (v:=v) (w:=6)
      intro k nu nv nb
      have ei := color _ (fun h => nu (hu k h)) (fun h => nb (blueSites i hi h).1)
      have ej := color _ (fun h => nv (hv k h)) (fun h => nb (blueSites j hj h).1)
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨ei,ej⟩
    · apply Fifteen.four_common_on_seven _ _ right ri color
        (Fifteen.union_three (sB _ (Fifteen.skip_ne zB _)) (sB _ (Fifteen.skip_ne zB _)))
      exact fun k => ⟨fun h => size (blueSites i hi h).2,fun h => size (blueSites j hj h).2⟩
  · have hj := mt agree.mpr hi
    apply Fifteen.four_common_on_seven _ _ left li color
      (Fifteen.union_three (sA _ (Fifteen.skip_ne zA i)) (sA _ (Fifteen.skip_ne zA j)))
    exact fun k => ⟨fun h => hi ⟨k,h⟩,fun h => hj ⟨k,h⟩⟩

end Ramsey556.Fourteen
