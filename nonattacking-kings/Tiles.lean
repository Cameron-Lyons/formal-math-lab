import Board

/-! Fix two adjacent columns. They hold 2k kings in the 2k aligned pairs
of rows, and each pair has room for one. Thus every pair contains one.
Sliding the two-column window one step shows that occupancy in each
pair of rows alternates across the entire board. -/
namespace Kings

def transpose (b : Board) : Board := fun r c => b c r

theorem IsPlacement.transpose {b : Board} {n k : Nat} (p : IsPlacement b n k) :
    IsPlacement (Kings.transpose b) n k where
  outside r c h := p.outside c r h.symm
  rowCount r hr := p.colCount r hr
  colCount c hc := p.rowCount c hc
  block r c := by
    have bound := p.block c r
    dsimp [Kings.transpose]
    omega

/-- Number of kings in column c of the i-th pair of rows. -/
private def inColumn (b : Board) (i c : Nat) : Nat := b (2*i) c + b (2*i+1) c

private theorem adjacent_columns {b : Board} {k i c : Nat} (p : IsPlacement b (4*k) k)
    (hi : i < 2*k) (hc : c+1 < 4*k) : inColumn b i c + inColumn b i (c+1) = 1 := by
  let row := fun r => b r c + b r (c+1)
  let pair := fun t => row (2*t) + row (2*t+1)
  have capacity (t : Nat) (_ : t < 2*k) : pair t ≤ 1 := by
    have bound := p.block (2*t) c
    dsimp [pair, row]
    omega
  have total : sumPrefix pair (2*k) = sumPrefix (fun _ => 1) (2*k) := by
    calc
      sumPrefix pair (2*k) = sumPrefix row (2*(2*k)) := sum_pairs row _
      _ = sumPrefix row (4*k) := by rw [show 2*(2*k) = 4*k by omega]
      _ = 2*k := by
        dsimp [row]
        rw [sumPrefix_add, p.colCount c (by omega), p.colCount (c+1) hc]
        omega
      _ = _ := (sum_ones _).symm
  have full := eq_at_of_sum_eq capacity total i hi
  dsimp [pair, row] at full
  dsimp [inColumn]
  omega

/-- Number of kings in the right column of tile (i,j). -/
def rightSide (b : Board) (i j : Nat) : Nat := inColumn b i (2*j+1)

/-- The horizontal offset is 1 when the king is on the right of its tile.
Read it in the first tile of the row pair. -/
def horizontal (b : Board) (i : Nat) : Nat := rightSide b i 0

/-- Transposing gives the vertical offset, with 1 for the bottom of the tile. -/
def vertical (b : Board) (j : Nat) : Nat := horizontal (transpose b) j

/-- Consecutive two-column windows have the same total (one). Cancelling
their common column shows that columns two steps apart have the same occupancy. -/
private theorem right_aligned {b : Board} {k i j : Nat} (p : IsPlacement b (4*k) k)
    (hi : i < 2*k) (hj : j < 2*k) : inColumn b i (2*j+1) = horizontal b i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have first := adjacent_columns (c := 2*j+1) p hi (by omega)
    have second := adjacent_columns (c := 2*j+1+1) p hi (by omega)
    have previous := ih (by omega)
    change inColumn b i (2*j+1+1+1) = horizontal b i
    omega

theorem horizontal_bound {b : Board} {k i : Nat} (p : IsPlacement b (4*k) k)
    (hi : i < 2*k) : horizontal b i ≤ 1 := by
  have full := adjacent_columns (c := 0) p hi (by omega)
  change inColumn b i (0+1) ≤ 1
  omega

theorem horizontal_sum {b : Board} {k : Nat} (p : IsPlacement b (4*k) k)
    (hk : 0 < k) : sumPrefix (horizontal b) (2*k) = k := by
  calc
    _ = sumPrefix (fun r => b r 1) (2*(2*k)) := sum_pairs _ _
    _ = k := by rw [show 2*(2*k) = 4*k by omega, p.colCount 1 (by omega)]

/-- Tile (i,j) has its king at the intersection of the chosen row and column. -/
theorem tile_entry {b : Board} {k i j u v : Nat} (p : IsPlacement b (4*k) k)
    (hi : i < 2*k) (hj : j < 2*k) (hu : u < 2) (hv : v < 2) :
    b (2*i+u) (2*j+v) = if u = vertical b j ∧ v = horizontal b i then 1 else 0 := by
  have full := adjacent_columns (c := 2*j) p hi (by omega)
  have right := right_aligned p hi hj
  have bottom : inColumn (transpose b) j (2*i+1) = vertical b j := right_aligned p.transpose hj hi
  dsimp [inColumn, transpose] at full right bottom
  -- Of the four corners, exactly the one with both offsets correct holds the king.
  rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl <;>
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl <;>
    (try simp only [Nat.add_zero]) <;> split <;> omega

end Kings
