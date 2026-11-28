import Ramsey556.Bipartite
import Ramsey556.SquarePaths

namespace Ramsey556

/-- In both halves the same color, green (1), runs between the two octets.
Each pair of sibling octets may have one missing green edge. -/
structure AlignedGreenHalves (c : Coloring 32) : Prop where
  inside : ∀ b i j, i ≠ j → c.edge (squareVertex b i) (squareVertex b j) ≠ 1
  siblings : ∃ bad : Fin 4 → Fin 8, ∀ a b i j, a ≠ b → a.val / 2 = b.val / 2 →
    (i ≠ bad a ∨ j ≠ bad b) → c.edge (squareVertex a i) (squareVertex b j) = 1

namespace AlignedOctets

private abbrev Slot := Fin 4 × Fin 4

/-- Slot zero is the first endpoint. A distinct second endpoint takes slot
one when required. The remaining slots avoid the exceptional edge endpoint. -/
private def order (a b bad : Fin 8) : Vector (Fin 8) 4 :=
  let fresh := (List.finRange 8).filter (fun x => x != a && x != b && x != bad)
  #v[a, if a = b then fresh[0]! else b, fresh[1]!, fresh[2]!]

private theorem order_spec : ∀ a b bad : Fin 8,
    (order a b bad)[0] = a ∧
    (a ≠ b → (order a b bad)[1] = b) ∧
    (∀ i j : Fin 4, (order a b bad)[i] = (order a b bad)[j] → i = j) ∧
    (a = b → ∀ i : Fin 4, i ≠ 0 → (order a b bad)[i] ≠ bad) := by decide

/-- Roles 0 and 1 form one pair of sibling octets, roles 2 and 3 the
other. The two cross-half edges start in role 0 and end in roles 2 and 3. -/
private def cycle (shared : Bool) : Vector Slot 9 :=
  if shared then
    #v[(0,0), (2,0), (3,1), (2,1), (3,2), (2,2), (3,3), (2,3), (3,0)]
  else
    #v[(0,0), (2,0), (3,1), (2,1), (3,2), (2,2), (3,0), (0,1), (1,1)]

private def arc (shared : Bool) (x y : Slot) : Prop :=
  (x = (0,0) ∧ y = (2,0)) ∨ (x = (0,if shared then 0 else 1) ∧ y = (3,0)) ∨
  (x.1 = 0 ∧ y.1 = 1 ∧ y.2 ≠ 0) ∨
  (x.1 = 2 ∧ y.1 = 3 ∧ (x.2 ≠ 0 ∨ y.2 ≠ 0))

private instance (s : Bool) (x y : Slot) : Decidable (arc s x y) := by unfold arc; infer_instance

private theorem cycle_spec : ∀ s : Bool,
    (∀ i j : Fin 9, (cycle s)[i] = (cycle s)[j] → i = j) ∧
    ∀ i : Fin 9, arc s (cycle s)[i] (cycle s)[i+1] ∨ arc s (cycle s)[i+1] (cycle s)[i] := by decide

private def bridge (c : Coloring 32) (a b : Fin 4) : Prop :=
  ∃ i j, c.edge (squareVertex a i) (squareVertex b j) = 1

private theorem bridge_symm (c : Coloring 32) {a b} : bridge c a b → bridge c b a := by
  rintro ⟨i, j, h⟩
  exact ⟨j, i, (c.symm _ _).trans h⟩

private theorem slot_inj (a b : Fin 4) (i j : Fin 8)
    (h : squareVertex a i = squareVertex b j) : a = b ∧ i = j := by
  have hv := congrArg Fin.val h
  dsimp [squareVertex] at hv
  exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩

private theorem block_order : ∀ a d b e : Fin 4, a ≠ d → a.val/2 = d.val/2 → b ≠ e →
        b.val/2 = e.val/2 → a.val/2 ≠ b.val/2 → ∀ i j : Fin 4,
        (#v[a,d,b,e])[i] = (#v[a,d,b,e])[j] → i = j := by decide

private theorem forkCycle (c : Coloring 32) (h : AlignedGreenHalves c)
    (a d b e : Fin 4) (had : a ≠ d) (hra : a.val / 2 = d.val / 2)
    (hbe : b ≠ e) (hrb : b.val / 2 = e.val / 2) (hr : a.val / 2 ≠ b.val / 2)
    (first : bridge c a b) (second : bridge c a e) : HasMonoC9 c := by
  obtain ⟨u, w, hfirst⟩ := first
  obtain ⟨v, z, hsecond⟩ := second
  obtain ⟨bad, siblings⟩ := h.siblings
  let shared := decide (u = v)
  let blocks := #v[a, d, b, e]
  let orders := #v[order u v (bad a), order 0 0 (bad d), order w w (bad b), order z z (bad e)]
  let embed (x : Slot) := squareVertex blocks[x.1] (orders[x.1])[x.2]
  have bi : ∀ i j : Fin 4, blocks[i] = blocks[j] → i = j := by
    exact block_order _ _ _ _ had hra hbe hrb hr
  have oi (r : Fin 4) : ∀ i j : Fin 4, (orders[r])[i] = (orders[r])[j] → i = j := by
    have : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> apply (order_spec _ _ _).2.2.1
  have inj (x y : Slot) (he : embed x = embed y) : x = y := by
    obtain ⟨hb, hs⟩ := slot_inj _ _ _ _ he
    have hb' := bi _ _ hb
    obtain ⟨r, i⟩ := x
    obtain ⟨s, j⟩ := y
    change r = s at hb'
    subst s
    exact Prod.ext rfl (oi _ _ _ hs)
  have secondEnd : (order u v (bad a))[(if shared then 0 else 1 : Fin 4)] = v := by
    by_cases huv : u = v
    · simpa [shared, huv] using (order_spec v v (bad a)).1
    · simpa [shared, huv] using (order_spec u v (bad a)).2.1 huv
  have green (x y : Slot) (he : arc shared x y) : c.edge (embed x) (embed y) = 1 := by
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hx, hy, hi⟩ | ⟨hx, hy, hi⟩
    · change c.edge (squareVertex a (order u v (bad a))[0]) (squareVertex b (order w w (bad b))[0]) = 1
      simpa only [(order_spec _ _ _).1] using hfirst
    · change c.edge (squareVertex a (order u v (bad a))[(if shared then 0 else 1 : Fin 4)])
          (squareVertex e (order z z (bad e))[0]) = 1
      simpa only [secondEnd, (order_spec _ _ _).1] using hsecond
    · simp only [embed, hx, hy]
      exact siblings a d _ _ had hra (Or.inr ((order_spec 0 0 (bad d)).2.2.2 rfl y.2 hi))
    · simp only [embed, hx, hy]
      exact siblings b e _ _ hbe hrb
        (hi.imp ((order_spec w w (bad b)).2.2.2 rfl x.2) ((order_spec z z (bad e)).2.2.2 rfl y.2))
  obtain ⟨simple, edges⟩ := cycle_spec shared
  refine ⟨1, fun i => embed (cycle shared)[i], fun {_ _} he => simple _ _ (inj _ _ he), ?_⟩
  intro i
  rcases edges i with h | h
  · exact green _ _ h
  · exact (c.symm _ _).trans (green _ _ h)

private def cut (flip : Bool) (a : Fin 4) : Bool :=
  (#v[false, true, flip, !flip])[a]

private def sameSidePair (flip : Bool) (a b : Fin 4) : Prop :=
  if flip then (a = 0 ∧ b = 3) ∨ (a = 1 ∧ b = 2)
  else (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 3)

private instance (f : Bool) (a b : Fin 4) : Decidable (sameSidePair f a b) := by
  unfold sameSidePair
  split <;> infer_instance

private theorem cut_pairs : ∀ f a b, a ≠ b → cut f a = cut f b →
    sameSidePair f a b ∨ sameSidePair f b a := by decide

private theorem use_cut (c : Coloring 32) (h : AlignedGreenHalves c) (flip : Bool)
    (avoid : ∀ a b, sameSidePair flip a b → ¬ bridge c a b) : IsBipartiteColor c 1 := by
  let block (u : Fin 32) : Fin 4 := ⟨u.val / 8, by omega⟩
  let slot (u : Fin 32) : Fin 8 := ⟨u.val % 8, by omega⟩
  have vertex (u) : squareVertex (block u) (slot u) = u := Fin.ext (by dsimp [squareVertex, block, slot]; omega)
  refine ⟨fun u => cut flip (block u), ?_⟩
  intro u v huv he hside
  have edge : c.edge (squareVertex (block u) (slot u)) (squareVertex (block v) (slot v)) = 1 := by
    rwa [vertex, vertex]
  have diff : block u ≠ block v := by
    intro eq
    have sn : slot u ≠ slot v := fun se => huv (by rw [← vertex u, eq, se, vertex])
    rw [← eq] at edge
    exact h.inside _ _ _ sn edge
  have conn : bridge c (block u) (block v) := ⟨slot u, slot v, edge⟩
  rcases cut_pairs flip _ _ diff hside with forward | backward
  · exact avoid _ _ forward conn
  · exact avoid _ _ backward (bridge_symm c conn)

end AlignedOctets

open AlignedOctets in
/-- When the two nearly complete bipartite graphs inside the halves share
color 1, the cross-half edges of that color must respect a common
bipartition. Two bridges from one octet to both octets of the other half
already produce a monochromatic C₉. -/
theorem aligned_halves_bipartite (c : Coloring 32) (h : AlignedGreenHalves c)
    (free : ¬ HasMonoC9 c) : IsBipartiteColor c 1 := by
  have noFork (a d b e : Fin 4) (had : a ≠ d) (ra : a.val / 2 = d.val / 2)
      (hbe : b ≠ e) (rb : b.val / 2 = e.val / 2) (rows : a.val / 2 ≠ b.val / 2)
      (first : bridge c a b) (second : bridge c a e) : False :=
    free (forkCycle c h a d b e had ra hbe rb rows first second)
  by_cases matched : bridge c 0 2 ∨ bridge c 1 3
  · apply use_cut c h true
    intro a b pair other
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases matched with first | first
    · exact noFork 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) first other
    · exact noFork 3 2 1 0 (by decide) (by decide) (by decide) (by decide) (by decide)
        (bridge_symm c first) (bridge_symm c other)
    · exact noFork 2 3 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (bridge_symm c first) (bridge_symm c other)
    · exact noFork 1 0 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) first other
  · apply use_cut c h false
    intro a b pair e
    rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact matched (Or.inl e)
    · exact matched (Or.inr e)

end Ramsey556
