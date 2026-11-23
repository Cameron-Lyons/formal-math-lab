import Ramsey556.FourteenSeven
import Ramsey556.AnchorClosure

namespace Ramsey556

/-- Exchange a named color with zero. -/
def swapZero (r k : Fin 3) : Fin 3 := if k = r then 0 else if k = 0 then r else k

@[simp] theorem swapZero_involutive : ∀ r k, swapZero r (swapZero r k) = k := by decide
theorem swapZero_injective (r : Fin 3) {a b : Fin 3} (h : swapZero r a = swapZero r b) : a = b := by
  simpa only [swapZero_involutive] using congrArg (swapZero r) h

@[simp] theorem swapZero_self : ∀ r, swapZero r r = 0 := by decide
@[simp] theorem swapZero_zero : ∀ r, swapZero r 0 = r := by decide

theorem swapZero_eq_iff (r a b : Fin 3) : swapZero r a = b ↔ a = swapZero r b := by
  constructor <;> intro h <;> simpa using congrArg (swapZero r) h

namespace Fourteen

theorem wide_shape (c : Coloring 33) (free : ¬ HasMonoC9 c) (v : Fin 14 → Fin 33)
    (vi : Function.Injective v) (miss : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ 0) :
    ∃ (t : Fin 8) (g b : Fin 3) (f : Fin 14 → Fin 14), t.val ≤ 6 ∧
      g ≠ 0 ∧ b ≠ 0 ∧ g ≠ b ∧ Function.Injective f ∧
      ∀ i j, i ≠ j → c.edge (v (f i)) (v (f j)) = if template14 true t i j then g else b := by
  have uses (i j : Fin 14) (ne : i ≠ j) : (c.induce v).edge i j = 1 ∨ (c.induce v).edge i j = 2 := by
    change c.edge _ _ = 1 ∨ c.edge _ _ = 2
    have := miss i j ne
    omega
  obtain ⟨wide,t,g,b,f,ht,colors,fi,edges⟩ := Fourteen.classify (c.induce v) 1 2 (by decide) uses
    (mt (HasMonoC9.of_induce vi) free)
  obtain ⟨g0,b0,gb⟩ : g ≠ 0 ∧ b ≠ 0 ∧ g ≠ b := by
    rcases colors with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> decide
  cases wide with
  | false =>
    obtain ⟨S⟩ := support_seven_seven c free (v ∘ f) (vi.comp fi)
      (fun _ _ ne => miss _ _ (fi.ne ne)) t ht g b g0 b0 gb edges
    exact (free (S.forces_cycle_of_size (by decide) twoColorOctets16)).elim
  | true => exact ⟨t,g,b,f,ht,g0,b0,gb,fi,edges⟩

theorem missing_after_swap (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (v : Fin 14 → Fin 33) (r : Fin 3) (miss : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) :
    ¬ HasMonoC9 (c.recolor (swapZero r)) ∧
    ∀ i j, i ≠ j → (c.recolor (swapZero r)).edge (v i) (v j) ≠ 0 := by
  refine ⟨mt (hasMonoC9_of_copy c id (swapZero r) Function.injective_id (@swapZero_injective r)) free, ?_⟩
  simpa [Coloring.recolor, swapZero_eq_iff] using miss

theorem edge_before_swap {c : Coloring 33} {r z w k}
    (h : (c.recolor (swapZero r)).edge z w = k) : c.edge z w = swapZero r k :=
  (swapZero_eq_iff r _ _).mp h

end Fourteen

/-- The part of the 14-vertex classification used on fifteen vertices. The wide template
contains a monochromatic clique on its first eight vertices. -/
theorem octet_of_missing_color14 (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (v : Fin 14 → Fin 33) (vi : Function.Injective v)
    (r : Fin 3) (miss : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) :
    ∃ (k : Fin 3) (a : Fin 8 → Fin 14), Function.Injective a ∧
      ∀ i j, i ≠ j → c.edge (v (a i)) (v (a j)) = k := by
  obtain ⟨df,miss'⟩ := Fourteen.missing_after_swap c free v r miss
  obtain ⟨t,g,_,f,_,_,_,_,fi,edges⟩ := Fourteen.wide_shape _ df v vi miss'
  let first : Fin 8 → Fin 14 := Fin.castLE (by decide)
  have inj : Function.Injective first := fun {_ _} h => Fin.ext (congrArg (fun x : Fin 14 => x.val) h)
  refine ⟨swapZero r g, f ∘ first, fi.comp inj, ?_⟩
  intro i j ne
  apply Fourteen.edge_before_swap
  simpa [template14, first, i.isLt, j.isLt] using edges (first i) (first j) (inj.ne ne)

end Ramsey556
