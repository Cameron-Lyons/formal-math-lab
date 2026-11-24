import Wall133.OddRadiusFive

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {n : ℕ}

/-- One internal detour and a two-vertex extension at the far end give an
induced path with four vertices more than the original edge length. -/
theorem detour_and_append (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {u : ℕ} (hu : 1 ≤ u) (hun : u+2 ≤ n) {x y : V}
    (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (w₁ : ∃ a, G.Adj x a ∧ Off P a (· = u))
    (w₂ : ∃ b, G.Adj x b ∧ Off P b (· = u+2))
    (w₃ : ∃ p, G.Adj y p ∧ Off P p (· = n)) : n+4 ≤ G.path := by
  obtain ⟨R,_,hyR,hcontacts⟩ := singleDetour P c h4 hu hun hx hy hxy w₁ w₂
  obtain ⟨p,hyp,hp⟩ := w₃
  have hpR := hcontacts hun hyp hp
  have hpGood : Good R.reverse p := by
    refine ⟨?_, ?_, ?_⟩
    · change G.Adj (R.vertex (n-1+2-0)) p
      exact ((hpR.contact _ (by omega)).2 (by omega)).symm
    · intro i hi
      exact hpR.fresh _ (Nat.sub_le _ _)
    · intro i hi hne ha
      have hi' := (hpR.contact (n-1+2-i) (Nat.sub_le _ _)).1 ha
      omega
  let Q := grow R.reverse p hpGood
  have hyGood : Good Q y := by
    refine ⟨hyp.symm, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact hyp.ne
      | succ i => exact hyR.fresh _ (Nat.sub_le _ _)
    · intro i hi hne ha
      cases i with
      | zero => exact hne rfl
      | succ i => exact (hyR.contact _ (Nat.sub_le _ _)).mp ha
  have hl := (grow Q y hyGood).length_le
  omega

end Wall133
