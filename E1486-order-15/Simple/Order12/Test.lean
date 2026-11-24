import Std.Tactic.BVDecide

/-! The finite test for order 12. A graph on 12 vertices is a string of 144 bits. -/

namespace E1486.Order12

abbrev Graph := BitVec 144

/-- Bit `12a+b` records the arrow `a → b`. -/
def edge (g : Graph) (a b : Nat) : Bool := g.getLsbD (12*a+b)

/-- Squaring on the square labels. The first `j` are fixed and the rest are
exchanged in consecutive pairs. This is the function `E1486.partner`. -/
def partner (j a : Nat) : Nat := if a < j then a else if (a-j)%2=0 then a+1 else a-1

/-- The arrow rules for a graph whose squares are the first `k` vertices. -/
def check (k j : Nat) (g : Graph) : Bool :=
  (List.range 12).all fun a =>
    -- 1. Some square points to a.
    (List.range k).any (fun q => edge g q a) &&
    -- 2. A square a has one closed route a → i → a, through its partner.
    -- A nonsquare has none.
    (List.range 12).all (fun i =>
      (edge g a i && edge g i a) == (decide (a < k) && i == partner j a)) &&
    -- 3. a reaches every square q by a two-step route.
    (List.range k).all (fun q => (List.range 12).any fun i => edge g a i && edge g i q) &&
    -- 4. Distinct middle vertices a,b cannot share both a predecessor x and
    -- a successor y: that would give two routes x → a → y and x → b → y.
    (List.range a).all fun b =>
      !((List.range 12).any fun x => edge g x a && edge g x b) ||
      !((List.range 12).any fun y => edge g a y && edge g b y)

/-- Write the test out bit by bit and pass it to the SAT solver. -/
macro "refute_pattern" : tactic => `(tactic|
  (dsimp [check, edge, partner, List.range, List.range.loop, List.all, List.any]
   bv_decide (config := {timeout := 600})))

end E1486.Order12
