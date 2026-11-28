import Std

namespace Ramsey556

/-- Three colors on the unordered edges of the complete graph.
The edge function's diagonal values are immaterial to simple cycles. -/
structure Coloring (n : Nat) where
  edge : Fin n → Fin n → Fin 3
  symm : ∀ u v, edge u v = edge v u

/-- Nine distinct vertices in cyclic order, with one color on all nine edges.
Addition in `Fin 9` supplies the closing edge from index 8 to index 0. -/
def HasMonoC9 {n : Nat} (c : Coloring n) : Prop :=
  ∃ (k : Fin 3) (v : Fin 9 → Fin n),
    Function.Injective v ∧ ∀ i, c.edge (v i) (v (i+1)) = k

/-- A C₉ entirely in a specified color. -/
def HasC9In {n : Nat} (c : Coloring n) (k : Fin 3) : Prop :=
  ∃ v : Fin 9 → Fin n, Function.Injective v ∧ ∀ i, c.edge (v i) (v (i+1)) = k

/-- Read a coloring on a chosen family of vertices. -/
def Coloring.induce {m n : Nat} (c : Coloring n) (v : Fin m → Fin n) : Coloring m where
  edge i j := c.edge (v i) (v j)
  symm _ _ := c.symm _ _

def Coloring.recolor {n : Nat} (c : Coloring n) (g : Fin 3 → Fin 3) : Coloring n where
  edge i j := g (c.edge i j)
  symm _ _ := congrArg g (c.symm _ _)

/-- An injective labeling carries a cycle in the induced graph back to the original graph. -/
theorem HasC9In.of_induce {m n k} {c : Coloring n} {v : Fin m → Fin n}
    (hv : Function.Injective v) : HasC9In (c.induce v) k → HasC9In c k := by
  rintro ⟨p, hp, edges⟩
  exact ⟨v ∘ p, hv.comp hp, edges⟩

theorem HasMonoC9.of_induce {m n} {c : Coloring n} {v : Fin m → Fin n}
    (hv : Function.Injective v) : HasMonoC9 (c.induce v) → HasMonoC9 c := by
  rintro ⟨k, cycle⟩
  exact ⟨k, HasC9In.of_induce hv cycle⟩

/-- Transfer a cycle after injective relabelings of vertices and colors. -/
theorem hasMonoC9_of_copy {m n : Nat} (c : Coloring n) (v : Fin m → Fin n) (g : Fin 3 → Fin 3)
    (hv : Function.Injective v) (hg : Function.Injective g) :
    HasMonoC9 ((c.induce v).recolor g) → HasMonoC9 c := by
  rintro ⟨k, p, hp, edges⟩
  refine ⟨c.edge (v (p 0)) (v (p (0+1))), v ∘ p, hv.comp hp, ?_⟩
  exact fun i => hg ((edges i).trans (edges 0).symm)

/-- The upper-bound assertion for the first open odd case of Erdős #556. -/
def K33Claim : Prop := ∀ c : Coloring 33, HasMonoC9 c

end Ramsey556
