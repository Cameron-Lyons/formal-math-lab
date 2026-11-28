import Std.Tactic.BVDecide

/-! The finite test. A graph on `n` vertices is a string of at least `n²` bits. -/

namespace E1486.Test

variable {w : Nat}

/-- Bit `n*a+b` records the arrow `a → b`. -/
def edge (n : Nat) (g : BitVec w) (a b : Nat) : Bool := g.getLsbD (n*a+b)

/-- Squaring on the square labels. The first `j` are fixed and the rest are
exchanged in consecutive pairs. This is the function `E1486.partner`. -/
def partner (j a : Nat) : Nat := if a < j then a else if (a-j)%2=0 then a+1 else a-1

/-- The arrow rules for a graph on `n` vertices whose squares are the first `k`. -/
def check (n k j : Nat) (g : BitVec w) : Bool :=
  (List.range n).all fun a =>
    -- 1. Some square points to a.
    (List.range k).any (fun q => edge n g q a) &&
    -- 2. A square a has one closed route a → i → a, through its partner.
    -- A nonsquare has none.
    (List.range n).all (fun i =>
      (edge n g a i && edge n g i a) == (decide (a < k) && i == partner j a)) &&
    -- 3. a reaches every square q by a two-step route.
    (List.range k).all (fun q => (List.range n).any fun i => edge n g a i && edge n g i q) &&
    -- 4. Distinct middle vertices a,b cannot share both a predecessor x and
    -- a successor y: that would give two routes x → a → y and x → b → y.
    (List.range a).all fun b =>
      !((List.range n).any fun x => edge n g x a && edge n g x b) ||
      !((List.range n).any fun y => edge n g a y && edge n g b y)

/-- Write the test out bit by bit and pass it to the SAT solver. -/
macro "refute_pattern" : tactic => `(tactic|
  (dsimp [check, edge, partner, List.range, List.range.loop, List.all, List.any]
   bv_decide (config := {timeout := 600})))

end E1486.Test
