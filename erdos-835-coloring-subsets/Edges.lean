import Mathlib.Combinatorics.SimpleGraph.Matching

namespace Erdos835

/-- A finite set paired by a symmetric, irreflexive relation has even cardinality. -/
theorem even_card_of_unique_partner {V : Type*} [Fintype V] (r : V → V → Prop)
    (hsymm : ∀ {x y}, r x y → r y x) (hirrefl : ∀ x, ¬ r x x)
    (hpartner : ∀ x, ∃! y, r x y) : Even (Fintype.card V) := by
  let G : SimpleGraph V := ⟨r, ⟨fun _ _ h => hsymm h⟩, ⟨hirrefl⟩⟩
  have hperfect : (⊤ : G.Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    simpa only [SimpleGraph.Subgraph.top_adj] using hpartner
  exact hperfect.even_card

/-- A permutation preserving a perfect matching pairs up its fixed vertices. -/
theorem even_fixed_of_matching {V : Type*} [DecidableEq V] (W : Finset V)
    (g : Equiv.Perm V) (hW : W.map g.toEmbedding = W) (R : V → V → Prop)
    (hsymm : ∀ {x y}, R x y → R y x) (hirrefl : ∀ x, ¬ R x x)
    (hpartner : ∀ x ∈ W, ∃! y : W, R x y.val)
    (hinv : ∀ {x y}, R x y → R (g x) (g y)) :
    Even (W.filter fun x => g x = x).card := by
  let F := W.filter fun x => g x = x
  suffices Even (Fintype.card F) by simpa [F] using this
  apply even_card_of_unique_partner (fun x y : F => R x y)
    (fun h => hsymm h) (fun x => hirrefl x)
  intro x
  obtain ⟨hxW, hx⟩ := Finset.mem_filter.mp x.property
  obtain ⟨y, hxy, huniq⟩ := hpartner x hxW
  have hgy : g y ∈ W := by
    simpa only [hW, Equiv.coe_toEmbedding] using Finset.mem_map_of_mem g.toEmbedding y.property
  have hfix : g y = y := by
    have h := hinv hxy
    rw [hx] at h
    exact congrArg Subtype.val (huniq ⟨g y, hgy⟩ h)
  refine ⟨⟨y, Finset.mem_filter.mpr ⟨y.property, hfix⟩⟩, hxy, ?_⟩
  intro z hz
  apply Subtype.ext
  exact congrArg (fun v : W => (v : V)) (huniq ⟨z, (Finset.mem_filter.mp z.property).1⟩ hz)

end Erdos835
