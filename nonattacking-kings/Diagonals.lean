import Tiles

namespace Kings

private theorem king_at {b : Board} {k i j : Nat} (p : IsPlacement b (4*k) k)
    (hi : i < 2*k) (hj : j < 2*k) :
    b (2*i + vertical b j) (2*j + horizontal b i) = 1 := by
  have row : vertical b j < 2 := Nat.lt_succ_of_le (horizontal_bound p.transpose hj)
  have col := Nat.lt_succ_of_le (horizontal_bound p hi)
  rw [tile_entry p hi hj row col, ite_eq_left ⟨rfl, rfl⟩]

private theorem bits_of_rise {a b : Nat} (inc : a < b) (bound : b ≤ 1) :
    a = 0 ∧ b = 1 := by omega

/-- Simultaneous rises put kings on the upper-right and lower-left corners
of the 2×2 square straddling the two tile boundaries. -/
theorem noRise {b : Board} {k : Nat} (p : IsPlacement b (4*k) k)
    (i j : Nat) (hi : i+1 < 2*k) (hj : j+1 < 2*k)
    (hh : horizontal b i < horizontal b (i+1))
    (hv : vertical b j < vertical b (j+1)) : False := by
  obtain ⟨h₀, h₁⟩ := bits_of_rise hh (horizontal_bound p hi)
  obtain ⟨v₀, v₁⟩ := bits_of_rise hv (horizontal_bound p.transpose hj)
  have upperRight := king_at (i := i) p (by omega) hj
  have lowerLeft := king_at (j := j) p hi (by omega)
  rw [v₁, h₀] at upperRight
  rw [v₀, h₁] at lowerLeft
  change b (2*i+1) (2*j+1+1) = 1 at upperRight
  change b (2*i+1+1) (2*j+1) = 1 at lowerLeft
  have square := p.block (2*i+1) (2*j+1)
  omega

/-- Simultaneous falls put kings on the upper-left and lower-right corners
of the same straddling square. -/
theorem noFall {b : Board} {k : Nat} (p : IsPlacement b (4*k) k)
    (i j : Nat) (hi : i+1 < 2*k) (hj : j+1 < 2*k)
    (hh : horizontal b (i+1) < horizontal b i)
    (hv : vertical b (j+1) < vertical b j) : False := by
  obtain ⟨h₁, h₀⟩ := bits_of_rise hh (horizontal_bound p (by omega))
  obtain ⟨v₁, v₀⟩ := bits_of_rise hv (horizontal_bound p.transpose (by omega))
  have upperLeft := king_at (i := i) (j := j) p (by omega) (by omega)
  have lowerRight := king_at p hi hj
  rw [v₀, h₀] at upperLeft
  rw [v₁, h₁] at lowerRight
  change b (2*i+1+1) (2*j+1+1) = 1 at lowerRight
  have square := p.block (2*i+1) (2*j+1)
  omega

end Kings
