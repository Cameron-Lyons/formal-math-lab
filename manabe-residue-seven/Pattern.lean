import Game

namespace SubtractionGame

/-- The length of the repeating block, three larger than the long move. -/
def period (k : Nat) : Nat := 11 * k + 10

/-- Read an index of the two-move word 00011100211. -/
def digit (r : Nat) : Nat :=
  match r with
  | 0 | 1 | 2 | 6 | 7 => 0
  | 8 => 2
  | _ => 1

/-- Extend the two-move word periodically from index zero. -/
def base (n : Nat) : Nat := digit (n % 11)

/-- Divide the prefix into rows of width q = 11(k+1). Rows 0, 1 and 2 read
the base word shifted by 0, 1 and 2 digits, with four exceptional cells. -/
def sample (k n : Nat) : Nat :=
  let q := period k + 1
  if n = period k then 3
  else if n = largeMove k ∨ n = q + 2 ∨ n = 2 * q + 1 then 2
  else base (n + if n < q then 0 else if n < 2 * q then 1 else 2)

end SubtractionGame
