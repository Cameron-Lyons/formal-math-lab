import Ramsey556.CleanSquare
import Ramsey556.Square

namespace Ramsey556

/-- The two cuts on 32 vertices suffice even when the new vertex breaks both cuts. -/
theorem hasMonoC9_of_bipartite_dropLast (c : Coloring 33)
    (hr : IsBipartiteColor (dropLast c) 0) (hs : IsBipartiteColor (dropLast c) 1) :
    HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  have baseFree := ((free_iff_compatible c).1 free).1
  obtain ⟨S⟩ := exists_cleanSquare (dropLast c) baseFree hr hs
  -- Enumerate each of the four cliques in the order given by the clean square.
  let block (u : Fin 32) : Fin 4 := ⟨u.val / 8, by omega⟩
  let slot (u : Fin 32) : Fin 8 := ⟨u.val % 8, by omega⟩
  let old (u : Fin 32) := S.vertex (block u) (slot u)
  have old_inj {i j : Fin 32} (h : old i = old j) : i = j := by
    obtain ⟨hb, hs⟩ := S.inj h
    have hb' := congrArg Fin.val hb
    have hs' := congrArg Fin.val hs
    dsimp [block, slot] at hb' hs'
    exact Fin.ext (by omega)
  have old_on (b : Fin 4) (s : Fin 8) : old (squareVertex b s) = S.vertex b s := by
    have h₁ : block (squareVertex b s) = b := Fin.ext (by dsimp [block, squareVertex]; omega)
    have h₂ : slot (squareVertex b s) = s := Fin.ext (by dsimp [slot, squareVertex]; omega)
    simp only [old, h₁, h₂]
  let v : Fin 33 → Fin 33 := Fin.lastCases (Fin.last 32) (fun u => (old u).castSucc)
  have hv {i j : Fin 33} (h : v i = v j) : i = j := by
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp only [v, Fin.lastCases_castSucc, Fin.lastCases_last] at h
    · rfl
    · have e := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at e
      omega
    · have e := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at e
      omega
    · exact congrArg Fin.castSucc (old_inj (Fin.castSucc_inj.mp h))
  -- The path table uses color 0 for the cliques. Exchange the names 0 and 2.
  let g (k : Fin 3) : Fin 3 := (#v[2, 1, 0] : Vector (Fin 3) 3)[k]
  have hg : ∀ (i j : Fin 3), g i = g j → i = j := by decide
  let copy := (c.induce v).recolor g
  have edge (a b : Fin 4) (i j : Fin 8) :
      (dropLast copy).edge (squareVertex a i) (squareVertex b j) =
      g ((dropLast c).edge (S.vertex a i) (S.vertex b j)) := by
    simp only [copy, dropLast, Coloring.induce, Coloring.recolor, v, Fin.lastCases_castSucc, old_on]
  have frame : SquareFrame (dropLast copy) := by
    constructor
    · intro b s t h
      rw [edge, S.inside _ _ _ h]
      rfl
    · intro a b s t hab row hs _
      have h₀ := S.row a b s t hab row
      have h₂ := S.clean a b s t hab hs
      have h₁ : (dropLast c).edge (S.vertex a s) (S.vertex b t) = 1 := by omega
      rw [edge, h₁]
      rfl
    · intro a b s t hab col hs _
      have h₁ := S.col a b s t hab col
      have h₂ := S.clean a b s t hab hs
      have h₀ : (dropLast c).edge (S.vertex a s) (S.vertex b t) = 0 := by omega
      rw [edge, h₀]
      rfl
  have bridge : squareBridge (dropLast copy) ≠ 0 := by
    unfold squareBridge
    rw [edge]
    intro h
    exact S.clean 0 3 0 0 (by decide) (by decide) (hg _ 2 h)
  exact free (hasMonoC9_of_copy c v g (@hv) (fun {_ _} => hg _ _)
    (hasMonoC9_of_squareFrame copy frame bridge))

end Ramsey556
