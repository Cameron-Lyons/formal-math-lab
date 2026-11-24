import Width43
import Projection

namespace Squares42

private abbrev ids := List.finRange 42

theorem only_remaining_rectangle {p w h} (t : Tiles p w h) (le : w ≤ h) :
    w = 77 ∧ h = 86 := by
  rcases remaining_rectangles t le with ⟨rfl, rfl⟩ | result
  · exact False.elim (no_width_43 p t)
  · exact result

private theorem cells_transpose (o : Cell) (w h : Nat) :
    ((cells o w h).map Prod.swap).Perm (cells o.swap h w) := by
  apply (List.perm_ext_iff_of_nodup _ (cells_nodup ..)).mpr
  · rintro ⟨x,y⟩
    constructor
    · intro hm
      obtain ⟨⟨v,u⟩, hu, eq⟩ := List.mem_map.mp hm
      change (u,v) = (x,y) at eq
      cases eq
      exact mem_cells.mpr (by have := mem_cells.mp hu; simp_all)
    · intro hm
      exact List.mem_map.mpr ⟨(y,x), mem_cells.mpr (by have := mem_cells.mp hm; simp_all), rfl⟩
  · apply List.pairwise_map.mpr
    apply (cells_nodup o w h).imp
    exact fun ne eq => ne (Prod.swap_inj.mp eq)

private theorem flatten_congr {α β} (l : List α) (f g : α → List β)
    (point : ∀ a, (f a).Perm (g a)) : (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact (point a).append ih

/-- Transposing every unit cell interchanges the dimensions of a tiling. -/
theorem transpose_tiles {p : Placement} {w h : Nat} (t : Tiles p w h) :
    Tiles (fun i => (p i).swap) h w := by
  have flipped := t.map Prod.swap
  rw [List.map_flatMap] at flipped
  have parts := flatten_congr ids _ _ (fun i => cells_transpose (p i) (side i) (side i))
  exact parts.symm.trans (flipped.trans (cells_transpose (0,0) w h))

theorem exists_tiling_iff_77_by_86 :
    (∃ (p : Placement) (w h : Nat), Tiles p w h) ↔ ∃ p : Placement, Tiles p 77 86 := by
  constructor
  · rintro ⟨p, w, h, t⟩
    by_cases le : w ≤ h
    · obtain ⟨rfl,rfl⟩ := only_remaining_rectangle t le
      exact ⟨p,t⟩
    · have t' := transpose_tiles t
      obtain ⟨rfl,rfl⟩ := only_remaining_rectangle t' (by omega)
      exact ⟨_,t'⟩
  · rintro ⟨p,t⟩
    exact ⟨p,77,86,t⟩

theorem projection_of_tiling {p : Placement} (t : Tiles p 43 154) :
    ∃ used live, SquareProjection.Reachable 154 used live :=
  (no_width_43 p t).elim

end Squares42
