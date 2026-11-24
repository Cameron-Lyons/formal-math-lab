import Std

/-!
A guillotine tiling is a square or the result of joining two guillotine
tilings across a full side. Rotation lets a single join constructor describe
both horizontal and vertical cuts. Stock entry `i` counts squares of side
`i + 1`. The tiling relation itself places no bound on multiplicities.
-/
namespace GuillotineSquares

abbrev Stock := Vector Nat 21

structure Block where
  width : Nat
  height : Nat
  stock : Stock
deriving DecidableEq, Inhabited

private instance : Hashable Block where
  hash b := hash (b.width, b.height, b.stock.toArray)

def square (s : Fin 21) : Block :=
  ⟨s.val + 1, s.val + 1, Vector.ofFn fun i => if i = s then 1 else 0⟩

def rotate (b : Block) : Block := ⟨b.height, b.width, b.stock⟩

def stack (a b : Block) : Block :=
  ⟨a.width, a.height + b.height, a.stock.zipWith (· + ·) b.stock⟩

inductive Guillotine : Block → Prop where
  | tile (s : Fin 21) : Guillotine (square s)
  | turn {b} : Guillotine b → Guillotine (rotate b)
  | join {a b} : Guillotine a → Guillotine b → a.width = b.width →
      Guillotine (stack a b)

def Legal (stock : Stock) : Prop := ∀ i : Fin 21, stock[i] ≤ 2

instance (stock : Stock) : Decidable (Legal stock) :=
  Nat.decidableForallFin (fun i : Fin 21 => stock[i] ≤ 2)

/-- Generate a list of candidate blocks grouped by their number of tiles.
The subsequent closure check establishes completeness independently of this
generation algorithm. -/
private def catalog : List Block := Id.run do
  let seeds : Array Block := (List.ofFn square).toArray
  let mut groups : Array (Array Block) := #[#[], seeds]
  for count in [2:43] do
    let mut group : Std.HashSet Block := {}
    for left in [1:count / 2 + 1] do
      for a in groups[left]! do
        for b in groups[count - left]! do
          if a.width == b.width then
            let c := stack a b
            if decide (Legal c.stock) then
              group := (group.insert c).insert (rotate c)
    groups := groups.push group.toArray
  return (groups.flatMap id).toList

private def acceptsJoin (a b : Block) : Bool :=
  if a.width = b.width then
    if Legal (stack a b).stock then catalog.contains (stack a b) else true
  else true

private theorem seedsChecked : ∀ i : Fin 21, square i ∈ catalog := by native_decide

private theorem turnsChecked : catalog.all (fun a => catalog.contains (rotate a)) = true := by
  native_decide

private theorem joinsChecked : catalog.all (fun a => catalog.all (acceptsJoin a)) = true := by
  native_decide

private theorem catalog_complete {b : Block} (h : Guillotine b) (legal : Legal b.stock) :
    b ∈ catalog := by
  induction h with
  | tile s => exact seedsChecked s
  | turn h ih =>
    exact List.contains_iff_mem.mp ((List.all_eq_true.mp turnsChecked) _ (ih legal))
  | @join a b _ _ hw iha ihb =>
    have bound (i : Fin 21) : a.stock[i] + b.stock[i] ≤ 2 := by
      simpa [stack, Vector.getElem_zipWith] using legal i
    have ha : Legal a.stock := fun i => Nat.le_trans (Nat.le_add_right _ _) (bound i)
    have hb : Legal b.stock := fun i => Nat.le_trans (Nat.le_add_left _ _) (bound i)
    have check := (List.all_eq_true.mp ((List.all_eq_true.mp joinsChecked) a (iha ha))) b (ihb hb)
    exact List.contains_iff_mem.mp (by simpa [acceptsJoin, hw, legal] using check)

private theorem areasChecked : catalog.all (fun b => b.width * b.height ≤ 4104) = true := by
  native_decide

/-- A guillotine rectangle with sides drawn from 1 through 21, each at most
twice, has area at most 4104. -/
theorem area_le_4104 {b : Block} (h : Guillotine b) (legal : Legal b.stock) :
    b.width * b.height ≤ 4104 := by
  exact of_decide_eq_true ((List.all_eq_true.mp areasChecked) b (catalog_complete h legal))

private abbrev Tiled := {b : Block // Guillotine b}

private def one (s : Nat) (lo : 0 < s := by decide) (hi : s ≤ 21 := by decide) : Tiled :=
  let i : Fin 21 := ⟨s - 1, by omega⟩
  ⟨square i, .tile i⟩

private def up (a b : Tiled) (h : a.val.width = b.val.width := by rfl) : Tiled :=
  ⟨stack a.val b.val, .join a.property b.property h⟩

private def side (a b : Tiled) (h : a.val.height = b.val.height := by rfl) : Tiled :=
  ⟨rotate (stack (rotate a.val) (rotate b.val)), .turn (.join (.turn a.property) (.turn b.property) h)⟩

/-- A 36 by 114 rectangle attains the bound. Each expression joins two
smaller rectangles vertically (`up`) or horizontally (`side`). -/
theorem area_4104_attained : ∃ b : Block, Guillotine b ∧ Legal b.stock ∧
    b.width = 36 ∧ b.height = 114 := by
  let row₁ := side (one 18) (one 18)
  let row₂ := side (up (side (up (one 3) (one 3)) (side (one 6) (one 6))) (one 15)) (one 21)
  let column₁ := up (side (one 7) (one 7)) (up (one 14) (one 14))
  let column₂ := up (side (up (one 2) (one 2)) (side (one 4) (one 4))) (up (one 10) (one 10))
  let row₃ := side column₁ (up (side (one 11) (one 11)) (side column₂ (up (one 12) (one 12))))
  let row₄ := side (up (side (one 8) (one 8)) (up (one 16) (one 16))) (up (one 20) (one 20))
  let whole := up row₁ (up row₂ (up row₃ row₄))
  exact ⟨whole.val, whole.property, by native_decide +revert, rfl, rfl⟩

/-- The required inventory, in ascending order of square size. -/
def twoEach : Stock := Vector.replicate 21 2

private theorem targetLegal : Legal twoEach := by native_decide

private theorem fullStockAbsent : catalog.all (fun b => b.stock != twoEach) = true := by
  native_decide

/-- No rectangle of any dimensions can be tiled with the specified 42 squares
by a recursive sequence of full horizontal or vertical cuts. -/
theorem no_guillotine_tiling (width height : Nat) :
    ¬ Guillotine ⟨width, height, twoEach⟩ := by
  intro h
  have member := catalog_complete h targetLegal
  have absent := (List.all_eq_true.mp fullStockAbsent) _ member
  simp at absent

end GuillotineSquares
