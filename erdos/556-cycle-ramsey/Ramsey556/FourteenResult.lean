import Ramsey556.FifteenResult
import Ramsey556.FourteenWide

namespace Ramsey556

/-- The two-colored 14-set has cliques of orders eight and six. At least three
exterior vertices each send two clique-colored edges, and no edge in the other
template color, into the six-clique. The map f only reorders the given 14-set. -/
def WideFourteen (c : Coloring 33) (v : Fin 14 → Fin 33) (r : Fin 3) : Prop :=
  ∃ (t : Fin 8) (green blue : Fin 3) (f : Fin 14 → Fin 14),
    t.val ≤ 6 ∧ green ≠ r ∧ blue ≠ r ∧ green ≠ blue ∧
    Function.Injective f ∧
    (∀ i j, i ≠ j → c.edge (v (f i)) (v (f j)) = if template14 true t i j then green else blue) ∧
    ∃ x : Fin 3 → Fin 33, Function.Injective x ∧
      (∀ a i, v (f a) ≠ x i) ∧ ∀ i, Fourteen.RichOnSix c (fun a => v (f a)) green blue (x i)

theorem wideFourteen_of_missing_color (c : Coloring 33) (free : ¬ HasMonoC9 c)
    (v : Fin 14 → Fin 33) (vi : Function.Injective v)
    (r : Fin 3) (miss : ∀ i j, i ≠ j → c.edge (v i) (v j) ≠ r) : WideFourteen c v r := by
  let d := c.recolor (swapZero r)
  obtain ⟨df,miss'⟩ := Fourteen.missing_after_swap c free v r miss
  obtain ⟨t,g,b,f,ht,g0,b0,gb,fi,edges⟩ := Fourteen.wide_shape d df v vi miss'
  obtain ⟨x,xi,dis,rich⟩ := Fourteen.wide_three_rich d df (v ∘ f) (vi.comp fi)
    (fun _ _ ne => miss' _ _ (fi.ne ne)) t g b g0 b0 gb edges
  have perm : Function.Injective (swapZero r) := @swapZero_injective r
  refine ⟨t,swapZero r g,swapZero r b,f,ht,?_,?_,perm.ne gb,fi,?_,x,@xi,dis,?_⟩
  · simpa [swapZero_eq_iff] using g0
  · simpa [swapZero_eq_iff] using b0
  · intro i j ne
    simpa [apply_ite] using Fourteen.edge_before_swap (edges i j ne)
  · simpa [Fourteen.RichOnSix, d, Coloring.recolor, swapZero_eq_iff, Function.comp_def] using rich

end Ramsey556
