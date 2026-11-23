import Ramsey556.Lower
import Ramsey556.NearBipartite

namespace Ramsey556

namespace Extension

/-- Shift within the eight-vertex block containing `u`. -/
private def shift (u : Fin 32) (j : Nat) : Fin 32 :=
  ⟨u.val / 8 * 8 + (u.val + j) % 8, by omega⟩

private def alternating (a b : Fin 32) (i : Fin 8) : Fin 32 :=
  if i.val % 2 = 0 then shift a (i.val / 2)
  else shift b ((i.val / 2 + 1) % 4)

private theorem shift_zero (a : Fin 32) : shift a 0 = a := Fin.ext (by simp [shift]; omega)

private theorem alternating_first (a b : Fin 32) : alternating a b 0 = a := by
  simpa [alternating] using shift_zero a

private theorem alternating_last (a b : Fin 32) : alternating a b 7 = b := by
  exact shift_zero b

private theorem alternating_inj (a b : Fin 32) (hab : a.val / 8 ≠ b.val / 8) :
    ∀ ⦃i j⦄, alternating a b i = alternating a b j → i = j := by
  intro i j hij
  have hv := congrArg Fin.val hij
  simp only [alternating] at hv
  split at hv <;> split at hv <;> simp [shift] at hv <;> exact Fin.ext (by omega)

private theorem shift_block (u : Fin 32) (j : Nat) : (shift u j).val / 8 = u.val / 8 := by
  dsimp [shift]
  omega

private theorem half_eq_of_block_eq {u v : Fin 32} (h : u.val / 8 = v.val / 8) :
    u.val / 16 = v.val / 16 := by
  change u.val / (8 * 2) = v.val / (8 * 2)
  rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

private theorem shift_half (u : Fin 32) (j : Nat) : (shift u j).val / 16 = u.val / 16 :=
  half_eq_of_block_eq (shift_block u j)

private theorem alternating_edges (a b : Fin 32) (i : Fin 8) (h : i.val + 1 < 8) :
    lowerColoring.edge (alternating a b i) (alternating a b ⟨i.val + 1, h⟩) =
      lowerColoring.edge a b := by
  dsimp [alternating]
  split <;> split <;> first
    | omega
    | solve | simp [lowerColoring, shift_block, shift_half, eq_comm]

/-- A seven-edge alternating path between different blocks uses only cross edges. -/
private theorem alternating_cross (a b : Fin 32) (hab : a.val / 8 ≠ b.val / 8)
    (i : Fin 8) (h : i.val + 1 < 8) :
    (alternating a b i).val / 8 ≠ (alternating a b ⟨i.val + 1, h⟩).val / 8 := by
  dsimp [alternating]
  split <;> split <;> simp only [shift_block] <;> omega

/-- Two distinct points in an octet cannot each be within the other's next
    three clockwise steps. Orient the edge so the four-point path avoids its tip. -/
private theorem canAvoid (a b : Fin 32) (hd : a ≠ b) :
    (∀ d : Fin 4, shift a d.val ≠ b) ∨ (∀ d : Fin 4, shift b d.val ≠ a) := by
  classical
  by_cases h : ∃ d : Fin 4, shift a d.val = b
  · right
    obtain ⟨i, hi⟩ := h
    intro j hj
    have hv := congrArg Fin.val hi
    have hw := congrArg Fin.val hj
    have hne : a.val ≠ b.val := fun h => hd (Fin.ext h)
    dsimp [shift] at hv hw
    omega
  · exact Or.inl (fun d he => h ⟨d, he⟩)

/-- An in-block edge in a cross-block color closes a nine-cycle using another
    block that is complete to the first one in that color. -/
private theorem closeInside (c : Coloring 33)
    (hold : ∀ a b : Fin 32, a.val / 8 ≠ b.val / 8 →
      c.edge a.castSucc b.castSucc = lowerColoring.edge a b)
    (u v : Fin 32) (same : u.val / 8 = v.val / 8)
    (avoid : ∀ d : Fin 4, shift u d.val ≠ v)
    (hk : c.edge v.castSucc u.castSucc ≠ 2) : HasMonoC9 c := by
  have partners : ∀ a : Fin 32, ∀ k : Fin 3, k ≠ 2 →
      ∃ b : Fin 32, a.val / 8 ≠ b.val / 8 ∧ lowerColoring.edge a b = k := by decide
  obtain ⟨y, huy, hcol⟩ := partners u _ hk
  apply closeC9Through c (lowerColoring.edge u y) (fun i => (alternating u y i).castSucc) v.castSucc
  · intro i j h
    exact alternating_inj u y huy (Fin.castSucc_inj.mp h)
  · intro i he
    have he' := Fin.castSucc_inj.mp he
    dsimp [alternating] at he'
    split at he'
    · exact avoid ⟨i.val / 2, by omega⟩ he'
    · have := congrArg (fun x : Fin 32 => x.val / 8) he'
      simp only [shift_block] at this
      omega
  · intro i h
    rw [hold _ _ (alternating_cross u y huy i h), alternating_edges]
  · simpa [alternating_first] using hcol.symm
  · rw [alternating_last, hold _ _ (by omega)]
    simp [lowerColoring, ← same, ← half_eq_of_block_eq same]

end Extension

/-- Every coloring of the 32 new edges to a single vertex extending the
    hierarchical lower-bound example creates a monochromatic simple 9-cycle. -/
theorem lowerColoring_extension_hasMonoC9 (c : Coloring 33)
    (hold : ∀ a b : Fin 32, a ≠ b → c.edge a.castSucc b.castSucc = lowerColoring.edge a b) :
    HasMonoC9 c := by
  have transfer (k : Fin 3) (h : IsBipartiteColor lowerColoring k) :
      IsBipartiteColor (dropLast c) k := by
    obtain ⟨side, hs⟩ := h
    exact ⟨side, fun u v he hcol => hs u v he ((hold u v he).symm.trans hcol)⟩
  exact hasMonoC9_of_bipartite_dropLast c (transfer 0 lowerColoring_two_bipartite.1)
    (transfer 1 lowerColoring_two_bipartite.2)

/-- It suffices to fix the edges between the four eight-vertex blocks of the
    template. All edges inside the blocks and at the 33rd vertex may be arbitrary. -/
theorem crossBlocks_hasMonoC9 (c : Coloring 33)
    (hold : ∀ a b : Fin 32, a.val / 8 ≠ b.val / 8 →
      c.edge a.castSucc b.castSucc = lowerColoring.edge a b) : HasMonoC9 c := by
  classical
  apply Classical.byContradiction
  intro hn
  apply hn
  apply lowerColoring_extension_hasMonoC9
  intro a b hne
  by_cases same : a.val / 8 = b.val / 8
  · have green : lowerColoring.edge a b = 2 := by
      simp [lowerColoring, same, Extension.half_eq_of_block_eq same]
    rw [green]
    apply Classical.byContradiction
    intro hk
    rcases Extension.canAvoid a b hne with ha | hb
    · exact hn (Extension.closeInside c hold a b same ha (by rwa [c.symm]))
    · exact hn (Extension.closeInside c hold b a same.symm hb hk)
  · exact hold a b same

end Ramsey556
