import Spacing
import Profiles
import Diagonals
import Constructions

/-!
# Nonattacking kings on a chessboard

## Why the board needs at least 4k columns

Choose a king in the second column. Take its row and a neighboring row, which
exists because n ≥ 2. Their 2k kings occupy distinct, nonconsecutive columns.
Within these two rows the first column is empty, since the second is occupied.
Pair each occupied column with its empty left neighbor. These 2k disjoint
pairs use 4k columns. This proves `lowerBound`.

The usual sharp spacing argument is also in `Spacing.lean`. In a strip of
length 2t+1, removing any odd-numbered column (counting from 1) leaves t
disjoint pairs of adjacent columns. Those pairs hold at most t kings. If the
strip holds t+1, every odd-numbered column must therefore be occupied.

## Why exactly two placements attain equality

1. **Look at two adjacent columns.** They hold 2k kings. Divide their cells
   into the 2k squares formed by pairing rows 1–2, 3–4, and so on. Each
   square holds at most one king, so each holds exactly one. Fix a pair of
   rows and slide the two-column window across the board. Every window
   contains one king, so occupied and empty columns alternate in that row pair.
   Transposing the argument gives the same alternation in each column pair.

2. **Record the corner of each tile.** Tile the board by aligned 2×2 squares.
   Each tile row now has a fixed horizontal choice (left or right), and each
   tile column has a fixed vertical choice (top or bottom). Together the
   two choices specify the king's corner in every tile. Each of the two
   lists is balanced. For example, the k kings in the second board column
   count precisely the tile rows choosing right.

3. **Look where two choices change.** Write left and top as 0, right and
   bottom as 1. If both lists have a 0→1 step, the upper-right and lower-left
   tiles where those steps cross have kings touching diagonally. Two 1→0
   steps give the other diagonal. If one list had both kinds of step, the
   other could never change. Yet each has k zeros and k ones. Thus one list
   rises once, the other falls once, and balance puts both changes at the midpoint.

4. **Check the two possibilities.** Choose which list rises. Each board row
   then has one king in each of the k tile columns selecting its vertical
   position, and the column count follows in the same way. Kings in
   horizontally neighboring tiles are two columns apart, and kings in
   vertically neighboring tiles are two rows apart. A diagonal attack would
   require steps in the same direction. Hence both choices give valid
   placements. They already differ in the first tile.

The arrows below show the occupied corner of every 2×2 tile in each
quadrant. The first diagram is `pattern k false` and the second is `pattern k true`.

```text
  ↙ │ ↖       ↗ │ ↘
 ───┼───     ───┼───
  ↘ │ ↗       ↖ │ ↙
```

The theorem `exactlyTwo` counts placements with board coordinates fixed.
-/
namespace Kings

private theorem pattern_of_offsets {b : Board} {k : Nat} (p : IsPlacement b (4*k) k)
    (flip : Bool)
    (H : ∀ i, i < 2*k → horizontal b i = midpointBit k flip i)
    (V : ∀ j, j < 2*k → vertical b j = midpointBit k (!flip) j) :
    b = pattern k flip := by
  funext r c
  by_cases inside : r < 4*k ∧ c < 4*k
  · obtain ⟨hr, hc⟩ := inside
    have hi : r/2 < 2*k := by omega
    have hj : c/2 < 2*k := by omega
    have cell := tile_entry (i := r/2) (j := c/2) (u := r%2) (v := c%2) p hi hj
      (by omega) (by omega)
    rw [show 2*(r/2)+r%2 = r by omega, show 2*(c/2)+c%2 = c by omega, H _ hi, V _ hj] at cell
    simpa only [pattern, hr, hc, true_and] using cell
  · have out : 4*k ≤ r ∨ 4*k ≤ c := by omega
    exact (p.outside r c out).trans ((pattern_isPlacement k flip).outside r c out).symm

/-- Every legal placement on the smallest possible board equals one of the
two explicit patterns, with the board coordinates held fixed. -/
theorem classifyPlacement {b : Board} {k : Nat} (hk : 0 < k) (p : IsPlacement b (4*k) k) :
    b = pattern k false ∨ b = pattern k true := by
  have profiles := classifyProfiles hk (horizontal b) (vertical b)
    (fun _ => horizontal_bound p) (fun _ => horizontal_bound p.transpose)
    (horizontal_sum p hk) (horizontal_sum p.transpose hk) (noRise p) (noFall p)
  rcases profiles with ⟨H, V⟩ | ⟨H, V⟩
  · exact Or.inl (pattern_of_offsets p false H V)
  · exact Or.inr (pattern_of_offsets p true H V)

/-- For every positive k, exactly two distinct labelled boards of side 4k
have k nonattacking kings in each row and each column. -/
theorem exactlyTwo {k : Nat} (hk : 0 < k) :
    ∃ a b : Board, a ≠ b ∧ ∀ x : Board, IsPlacement x (4*k) k ↔ x = a ∨ x = b := by
  refine ⟨pattern k false, pattern k true, patterns_ne hk, fun x => ⟨classifyPlacement hk, ?_⟩⟩
  rintro (rfl | rfl) <;> exact pattern_isPlacement _ _

end Kings
