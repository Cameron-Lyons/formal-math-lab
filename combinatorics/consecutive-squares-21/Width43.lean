import Squares

/-! A direct proof for the 43 × 154 rectangle.

Every row meets exactly three squares. Each unit square belongs to a row
of widths 21, 21, 1, so the two 21-squares overlap for two rows. For the
next 19 rows just one of them continues. Its two neighbors start together
and their widths add to 22.

Suppose their widths are a < b. When just one square ends, its replacement
has the same width. To change widths, the two stacks must end together.
The smaller stack can reach at most 2a, so this would require 2a = b.
That is impossible because a + b = 22. The same two widths must therefore
span 19 rows, forcing 10 and 12. Both stacks extend beyond row 19, which
requires a third 21. Thus the two new squares both have width 11.
Reading the rows in reverse requires two more 11s. -/

namespace Squares42

theorem mem_active_iff {p : Placement} {i : Tile} {y : Nat} :
    i ∈ active p y ↔ (p i).2 ≤ y ∧ y < (p i).2 + side i := by
  simp [active]

private theorem row_triple {p y} (t : Tiles p 43 154) (hy : y < 154) :
    ∃ a b c : Tile, active p y = [a,b,c] ∧
      a.val < b.val ∧ b.val < c.val ∧ side a + side b + side c = 43 := by
  let row := active p y
  obtain ⟨a, b, c, e⟩ : ∃ a b c : Tile, row = [a,b,c] :=
    ⟨_, _, _, List.eq_getElem_of_length_eq_three _ (row_three t hy)⟩
  have width : (row.map side).sum = 43 := row_width t hy
  have ordered : row.Pairwise (· < ·) := (List.pairwise_lt_finRange 42).filter _
  rw [e] at width ordered
  simp [List.pairwise_cons, Fin.lt_def] at ordered
  exact ⟨a, b, c, e, ordered.1.1, ordered.2, by simpa [Nat.add_assoc] using width⟩

/-- In a unit-square row the other two squares must both have side 21. -/
private theorem special_tiles {p y} (t : Tiles p 43 154) (hy : y < 154) :
    let row := active p y
    ((40 ∈ row ∧ 41 ∈ row) ↔ (0 ∈ row ∨ 1 ∈ row)) ∧ ¬(0 ∈ row ∧ 1 ∈ row) := by
  obtain ⟨a,b,c,row,ab,bc,width⟩ := row_triple t hy
  simp [row, Fin.ext_iff]
  have := c.isLt
  simp only [side] at width
  omega

/-- The two rows occupied by the unit squares are precisely the common rows of
the two 21-squares. -/
theorem big_overlap {p : Placement} (t : Tiles p 43 154) (y : Nat) :
    ((p 40).2 ≤ y ∧ y < (p 40).2 + 21 ∧ (p 41).2 ≤ y ∧ y < (p 41).2 + 21) ↔
    y = (p 0).2 ∨ y = (p 1).2 := by
  by_cases hy : y < 154
  · have eq := (special_tiles t hy).1
    simp only [mem_active_iff] at eq
    change ((_ ∧ y < _ + 21) ∧ (_ ∧ y < _ + 21) ↔
      (_ ∧ y < _ + 1) ∨ (_ ∧ y < _ + 1)) at eq
    omega
  · have a := (inside t 0).2
    have b := (inside t 1).2
    have c := (inside t 40).2
    change _ + 1 ≤ 154 at a b
    change _ + 21 ≤ 154 at c
    omega

/-- The starting heights of the two 21-squares differ by 19. -/
theorem big_starts {p : Placement} (t : Tiles p 43 154) :
    (p 40).2 + 19 = (p 41).2 ∨ (p 41).2 + 19 = (p 40).2 := by
  have hu := (inside t 0).2
  change _ + 1 ≤ 154 at hu
  have distinct := (special_tiles t (show (p 0).2 < 154 by omega)).2
  simp only [mem_active_iff] at distinct
  change ¬((_ ∧ _ < _ + 1) ∧ (_ ∧ _ < _ + 1)) at distinct
  have u := (big_overlap t ((p 0).2)).mpr (Or.inl rfl)
  have v := (big_overlap t ((p 1).2)).mpr (Or.inr rfl)
  let start := max (p 40).2 (p 41).2
  have r₀ := big_overlap t start
  have r₁ := big_overlap t (start + 1)
  have r₂ := big_overlap t (start + 2)
  dsimp [start] at r₀ r₁ r₂
  omega

/-- The other two squares in a row meeting the given square. -/
private theorem neighbors {p : Placement} (t : Tiles p 43 154) {z : Nat} {g : Tile}
    (hg : g ∈ active p z) :
    ∃ a b, (∀ i, i ∈ active p z ↔ i = g ∨ i = a ∨ i = b) ∧
      g ≠ a ∧ g ≠ b ∧ a ≠ b ∧ side g + side a + side b = 43 := by
  have hz := Nat.lt_of_lt_of_le (mem_active_iff.mp hg).2 (inside t g).2
  obtain ⟨u,v,w,row,uv,vw,sum⟩ := row_triple t hz
  simp only [row, List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  rcases hg with rfl | rfl | rfl
  · exact ⟨v, w, by grind⟩
  · exact ⟨u, w, by grind⟩
  · exact ⟨u, v, by grind⟩

private theorem third_tile {p : Placement} (t : Tiles p 43 154) {z : Nat} {g b : Tile}
    (hg : g ∈ active p z) (hb : b ∈ active p z) (hgb : g ≠ b) :
    ∃ a, a ∈ active p z ∧ a ≠ g ∧ a ≠ b ∧ side g + side b + side a = 43 ∧
      ∀ i ∈ active p z, i = g ∨ i = b ∨ i = a := by
  obtain ⟨u,v,mem,gu,gv,uv,sum⟩ := neighbors t hg
  rcases (mem b).mp hb with e | rfl | rfl
  · exact (hgb e.symm).elim
  · exact ⟨v, by grind⟩
  · exact ⟨u, by grind⟩

private theorem two_per_size {i j k : Tile} (ij : side i = side j) (ik : side i = side k) :
    i = j ∨ i = k ∨ j = k := by
  simp only [Fin.ext_iff, side] at *
  omega

/-- The two continuing squares force the outgoing square to repeat when it ends. -/
private theorem replacement {p : Placement} (t : Tiles p 43 154) {z : Nat} {g b a : Tile}
    (hg : (p g).2 < z ∧ z < (p g).2 + side g)
    (hb : (p b).2 < z ∧ z < (p b).2 + side b)
    (ha : (p a).2 + side a = z)
    (gb : side g ≠ side b) (ga : side g ≠ side a) (ba : side b ≠ side a)
    (w : side g + side b + side a = 43) :
    ∃ i, side i = side a ∧ (p i).2 = z := by
  have pos : 0 < side a := by simp [side]
  have gb' : g ≠ b := fun e => gb (congrArg side e)
  obtain ⟨c,_,_,_,_,prior⟩ := third_tile (z := z-1) (g := g) (b := b) t
    (mem_active_iff.mpr (by omega)) (mem_active_iff.mpr (by omega)) gb'
  have ac : a = c := by
    rcases prior a (mem_active_iff.mpr (by omega)) with e | e | e
    · exact (ga (congrArg side e.symm)).elim
    · exact (ba (congrArg side e.symm)).elim
    · exact e
  obtain ⟨i,hi,ig,ib,width,_⟩ := third_tile (z := z) (g := g) (b := b) t
    (mem_active_iff.mpr (by omega)) (mem_active_iff.mpr (by omega)) gb'
  have absent : i ∉ active p (z-1) := by
    intro hz
    rcases prior i hz with e | e | e
    · exact ig e
    · exact ib e
    · have ia : i = a := e.trans ac.symm
      have := mem_active_iff.mp (ia ▸ hi : a ∈ active p z)
      omega
  have := mem_active_iff.mp hi
  rw [mem_active_iff] at absent
  exact ⟨i, by omega, by omega⟩

/-- An unequal pair cannot fill the width 22 beside the surviving 21-square. -/
private theorem unequal_split {p : Placement} (t : Tiles p 43 154) {y : Nat} {g a b : Tile}
    (sg : side g = 21) (band : ∀ d, d < 19 → g ∈ active p (y+d))
    (stop : ∀ i ∈ active p (y+19), side i ≠ 21)
    (sa : (p a).2 = y) (sb : (p b).2 = y) (lt : side a < side b)
    (sum : side a + side b = 22) : False := by
  have g₀ := mem_active_iff.mp (band 0 (by decide))
  have g₁ := mem_active_iff.mp (band 18 (by decide))
  have pos : 0 < side a := by simp [side]
  have bSmall : side b < 21 := by
    by_cases h : side b ≥ 21
    · exact False.elim (stop b (mem_active_iff.mpr (by omega)) (by omega))
    · omega
  -- The smaller square ends first and must be replaced by its twin.
  have smallTwin : ∃ i, side i = side a ∧ (p i).2 = y + side a := by
    apply replacement (g := g) (b := b) (a := a) t <;> omega
  obtain ⟨a', sameA, startA⟩ := smallTwin
  let k := min (2 * side a) 19
  -- The wider track is still occupied when the second small square or the 21 ends.
  have wide : ∃ b', side b' = side b ∧ b' ∈ active p (y+k) := by
    by_cases long : k < side b
    · exact ⟨b, rfl, mem_active_iff.mpr (by omega)⟩
    · have dif : side b ≠ 2 * side a := by omega
      have early : side b < k := by dsimp [k] at *; omega
      have wideTwin : ∃ i, side i = side b ∧ (p i).2 = y + side b := by
        apply replacement (g := g) (b := a') (a := b) t <;> dsimp [k] at * <;> omega
      obtain ⟨b', sameB, startB⟩ := wideTwin
      exact ⟨b',sameB,mem_active_iff.mpr (by dsimp [k]; omega)⟩
  obtain ⟨b', sameB, activeB⟩ := wide
  by_cases early : 2 * side a < 19
  · -- A third small square would be needed.
    have activeG := band k (by dsimp [k]; omega)
    obtain ⟨a'',activeA,_,_,width,_⟩ := third_tile t activeG activeB
      (fun e => by have := congrArg side e; omega)
    have tri := two_per_size (i := a) (j := a') (k := a'') sameA.symm (by omega)
    have span := mem_active_iff.mp activeA
    dsimp [k] at span
    rcases tri with e | e | e <;> subst_vars <;> omega
  · -- Here the pair is 10 and 12. Both tracks continue past the last row of the 21.
    have k19 : k = 19 := by dsimp [k]; omega
    rw [k19] at activeB
    have activeA : a' ∈ active p (y+19) := mem_active_iff.mpr (by omega)
    obtain ⟨c,hc,_,_,w,_⟩ := third_tile t activeA activeB
      (fun e => by have := congrArg side e; omega)
    exact stop c hc (by omega)

/-- On the first row beyond the overlap, both new squares have side 11. -/
theorem strip_elevens {p : Placement} (t : Tiles p 43 154) (y : Nat) (g : Tile)
    (sg : side g = 21) (band : ∀ d, d < 19 → g ∈ active p (y+d))
    (start : ∀ i ∈ active p y, i ≠ g → (p i).2 = y)
    (stop : ∀ i ∈ active p (y+19), side i ≠ 21) :
    ∃ a b : Tile, a ≠ b ∧ side a = 11 ∧ side b = 11 ∧ (p a).2 = y ∧ (p b).2 = y := by
  have hg := band 0 (by decide)
  rw [Nat.add_zero] at hg
  obtain ⟨a,b,mem,ga,gb,ab,sum⟩ := neighbors t hg
  have sa := start a ((mem a).mpr (by simp)) (Ne.symm ga)
  have sb := start b ((mem b).mpr (by simp)) (Ne.symm gb)
  by_cases lt : side a < side b
  · exact (unequal_split t sg band stop sa sb lt (by omega)).elim
  by_cases gt : side b < side a
  · exact (unequal_split t sg band stop sb sa gt (by omega)).elim
  exact ⟨a,b,ab,by omega,by omega,sa,sb⟩

/-- Immediately beyond the common rows of the 21-squares, both 11-squares
must begin. In particular, the first one (tile 20) begins there. -/
private theorem eleven_above {p : Placement} (t : Tiles p 43 154)
    (lo hi : Tile) (slo : side lo = 21) (shi : side hi = 21)
    (both : ∀ i, side i = 21 → i = lo ∨ i = hi)
    (gap : (p lo).2 + 19 = (p hi).2) : (p 20).2 = (p lo).2 + 21 := by
  let y := (p lo).2 + 21
  have before (i : Tile) (s : side i = 21) : i ∈ active p (y-1) := by
    apply mem_active_iff.mpr
    rcases both i s with rfl | rfl <;> dsimp [y] <;> omega
  -- The preceding row contains the two 21-squares and a unit square.
  have distinct : lo ≠ hi := by rintro rfl; omega
  obtain ⟨unit, _, _, _, sum, only⟩ := third_tile t (before lo slo) (before hi shi) distinct
  have unitSide : side unit = 1 := by omega
  have starts (i : Tile) (on : i ∈ active p y) (other : i ≠ hi) : (p i).2 = y := by
    have current := mem_active_iff.mp on
    apply Decidable.byContradiction
    intro h
    have prior : i ∈ active p (y-1) := mem_active_iff.mpr (by dsimp [y] at *; omega)
    rcases only i prior with rfl | rfl | rfl
    · dsimp [y] at current
      omega
    · exact other rfl
    · omega
  have band (d : Nat) (hd : d < 19) : hi ∈ active p (y+d) := by
    apply mem_active_iff.mpr
    dsimp [y]
    omega
  have stop (i : Tile) (on : i ∈ active p (y+19)) (big : side i = 21) : False := by
    have := mem_active_iff.mp on
    rcases both i big with rfl | rfl <;> dsimp [y] at * <;> omega
  obtain ⟨a,b,ne,sa,sb,ha,hb⟩ := strip_elevens t y hi shi band starts stop
  have : a.val ≠ b.val := fun h => ne (Fin.ext h)
  have which : a = 20 ∨ b = 20 := by
    simp only [side] at sa sb
    simp only [Fin.ext_iff]
    omega
  rcases which with rfl | rfl
  · exact ha
  · exact hb

private theorem first_eleven {p : Placement} (t : Tiles p 43 154) :
    (p 20).2 = min (p 40).2 (p 41).2 + 21 := by
  have both (i : Tile) (s : side i = 21) : i = 40 ∨ i = 41 := by
    simp only [side] at s
    simp only [Fin.ext_iff]
    omega
  rcases big_starts t with h | h
  · have := eleven_above t 40 41 (by decide) (by decide) both h
    omega
  · have := eleven_above t 41 40 (by decide) (by decide) (fun i s => (both i s).symm) h
    omega

/-- Reflect a placement across the horizontal midline of a board of height h. -/
def flipY (h : Nat) (p : Placement) : Placement := fun i =>
  ((p i).1, h - ((p i).2 + side i))

theorem flipY_tiles {p w h} (t : Tiles p w h) : Tiles (flipY h p) w h := by
  have valid := check_iff_tiles.mpr t
  apply check_iff_tiles.mp
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, forall_const] at valid ⊢
  refine ⟨valid.1, fun i => ⟨?_, fun j => ?_⟩⟩
  · have bound := (valid.2 i).1
    dsimp [flipY]
    omega
  · rcases (valid.2 i).2 j with eq | apart
    · exact Or.inl eq
    · right
      have bi := (valid.2 i).1.2
      have bj := (valid.2 j).1.2
      simp only [Apart, flipY] at apart ⊢
      omega

/-- The two 11-squares would have to lie on both sides of the overlap. -/
theorem no_width_43 (p : Placement) : ¬ Tiles p 43 154 := by
  intro t
  have above := first_eleven t
  have below := first_eleven (flipY_tiles t)
  have gap := big_starts t
  have bound := (inside t 20).2
  change (p 20).2 + 11 ≤ 154 at bound
  change 154 - ((p 20).2 + 11) =
    min (154 - ((p 40).2 + 21)) (154 - ((p 41).2 + 21)) + 21 at below
  omega

end Squares42
