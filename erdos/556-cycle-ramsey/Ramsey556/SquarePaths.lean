import Ramsey556.Extension

namespace Ramsey556

/-- Eight vertices in each of four blocks arranged as a two-by-two square. -/
def squareVertex (b : Fin 4) (s : Fin 8) : Fin 32 := ⟨8 * b.val + s.val, by omega⟩

/-- The two vertices per block at which we inspect the new incident colors. -/
def squareSample (b : Fin 4) (s : Fin 2) : Fin 32 :=
  squareVertex b ⟨s.val + 1, by omega⟩

/-- All eight vertices in each block form a color-0 clique. On slots 0 through
4 in every block, cross-block edges in the same row have color 1 and those in
the same column have color 2. -/
structure SquareFrame (c : Coloring 32) : Prop where
  inside : ∀ b s t, s ≠ t → c.edge (squareVertex b s) (squareVertex b t) = 0
  row : ∀ (a b : Fin 4) (s t : Fin 8), a ≠ b → a.val / 2 = b.val / 2 →
    s.val < 5 → t.val < 5 → c.edge (squareVertex a s) (squareVertex b t) = 1
  col : ∀ (a b : Fin 4) (s t : Fin 8), a ≠ b → a.val % 2 = b.val % 2 →
    s.val < 5 → t.val < 5 → c.edge (squareVertex a s) (squareVertex b t) = 2

/-- One edge connecting diagonally opposite blocks. -/
def squareBridge (c : Coloring 32) : Fin 3 := c.edge (squareVertex 0 0) (squareVertex 3 0)

/-- Conditions under which a pair of sample vertices has a path of seven
edges in color `k`. A bridge of color 1 or 2 connects its two components. -/
def SquareConflict (bridge k : Fin 3) (a b : Fin 4) (s t : Fin 2) : Prop :=
  (k = 0 ∧ a = b ∧ s ≠ t) ∨
  (k = 1 ∧ a.val % 2 ≠ b.val % 2 ∧ (a.val / 2 = b.val / 2 ∨ bridge = 1)) ∨
  (k = 2 ∧ a.val / 2 ≠ b.val / 2 ∧ (a.val % 2 = b.val % 2 ∨ bridge = 2))

instance (d k : Fin 3) (a b : Fin 4) (s t : Fin 2) :
    Decidable (SquareConflict d k a b s t) := by
  unfold SquareConflict
  infer_instance

private abbrev Slot := Fin 4 × Fin 8

private def vertex (x : Slot) : Fin 32 := squareVertex x.1 x.2

private theorem vertex_injective (x y : Slot) (h : vertex x = vertex y) : x = y := by
  have eq := congrArg Fin.val h
  change 8 * x.1.val + x.2.val = 8 * y.1.val + y.2.val at eq
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- The edges directly available from the frame and its one diagonal bridge. -/
private def Available (d k : Fin 3) (x y : Slot) : Prop :=
  (k = 0 ∧ x.1 = y.1 ∧ x.2 ≠ y.2) ∨
  (k = 1 ∧ x.1 ≠ y.1 ∧ x.1.val / 2 = y.1.val / 2 ∧ x.2.val < 5 ∧ y.2.val < 5) ∨
  (k = 2 ∧ x.1 ≠ y.1 ∧ x.1.val % 2 = y.1.val % 2 ∧ x.2.val < 5 ∧ y.2.val < 5) ∨
  (d = k ∧ ((x = (0, 0) ∧ y = (3, 0)) ∨ (x = (3, 0) ∧ y = (0, 0))))

private instance (d k : Fin 3) (x y : Slot) : Decidable (Available d k x y) := by
  unfold Available
  infer_instance

private theorem availableEdge {c : Coloring 32} (hc : SquareFrame c) {k : Fin 3}
    {x y : Slot} (h : Available (squareBridge c) k x y) :
    c.edge (vertex x) (vertex y) = k := by
  rcases h with ⟨rfl, hrow, hslot⟩ | ⟨rfl, hbloc, hside, hx, hy⟩ |
      ⟨rfl, hbloc, hside, hx, hy⟩ | ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · simpa only [vertex, hrow] using hc.inside y.1 x.2 y.2 hslot
  · exact hc.row _ _ _ _ hbloc hside hx hy
  · exact hc.col _ _ _ _ hbloc hside hx hy
  · rfl
  · exact c.symm _ _

private def sampleSlot (s : Fin 2) : Fin 8 := ⟨s.val + 1, by omega⟩

/-- Partner of a block in a complete bipartite row or column. -/
private def mate (k : Fin 3) (a : Fin 4) : Fin 4 :=
  if k = 1 then (#v[1, 0, 3, 2] : Vector (Fin 4) 4)[a]
  else (#v[2, 3, 0, 1] : Vector (Fin 4) 4)[a]

private def path (k : Fin 3) (a b : Fin 4) (s t : Fin 2) : Vector Slot 8 :=
  let u := sampleSlot s
  let v := sampleSlot t
  if k = 0 then
    -- Sweep a whole block between its two samples.
    #v[(a,u), (a,0), (a,3), (a,4), (a,5), (a,6), (a,7), (b,v)]
  else if mate k a = b then
    -- Alternate between the two blocks of the row or column.
    #v[(a,u), (b,0), (a,0), (b,3), (a,3), (b,4), (a,4), (b,v)]
  else if a = 0 ∨ a = 3 then
    -- The endpoints lie in the bridge blocks. Use two edges before the bridge and four after.
    #v[(a,u), (mate k a,0), (a,0), (b,0), (mate k b,0), (b,3), (mate k b,1), (b,v)]
  else
    -- The endpoints lie in the other blocks. Use three edges on each side of the bridge.
    #v[(a,u), (mate k a,3), (a,3), (mate k a,0), (mate k b,0), (b,3), (mate k b,3), (b,v)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem path_certificate : ∀ (d k : Fin 3) (a b : Fin 4) (s t : Fin 2),
    SquareConflict d k a b s t →
      let p := path k a b s t
      p[0] = (a, sampleSlot s) ∧ p[7] = (b, sampleSlot t) ∧
      (∀ i j : Fin 8, p[i] = p[j] → i = j) ∧
      (∀ (i : Fin 8) (h : i.val + 1 < 8), Available d k p[i] p[i.val+1]) := by
  decide

/-- Each required conflict is realized by a simple seven-edge path. -/
theorem squareFrame_conflict (c : Coloring 32) (hc : SquareFrame c) (k : Fin 3)
    (a b : Fin 4) (s t : Fin 2) (h : SquareConflict (squareBridge c) k a b s t) :
    Conflict c k (squareSample a s) (squareSample b t) := by
  obtain ⟨h0, h7, hi, he⟩ := path_certificate _ _ _ _ _ _ h
  let p := path k a b s t
  refine ⟨(fun i => vertex p[i]), ?_, congrArg vertex h0, congrArg vertex h7, ?_⟩
  · exact fun {i j} eq => hi i j (vertex_injective _ _ eq)
  · intro i h
    exact availableEdge hc (he i h)

end Ramsey556
