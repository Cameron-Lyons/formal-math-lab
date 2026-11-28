import Simple.Test

/-! Ordering conditions for the finite test.

Read a fixed list of arrows of a graph as a string of bits. Among the tables that satisfy
the law with a given pattern of squares, one makes this string as large as possible, and
then no relabeling that keeps the pattern increases it. The test asks this of a few swaps
of neighboring labels. `Simple.LeaderOfLaw` proves that if a table satisfies the law, then
so does one that passes this test. -/

namespace E1486.Test

variable {w : Nat}

/-- The arrows that are compared, most significant first: those among the `k` squares,
then for each nonsquare its arrows from the squares and its arrows to the squares. -/
def cells (n k : Nat) : List (Nat × Nat) :=
  ((List.range k).flatMap fun x => (List.range k).map fun y => (x,y)) ++
  (List.range (n-k)).flatMap fun i =>
    (List.range k).map (fun q => (q,k+i)) ++ (List.range k).map (fun q => (k+i,q))

/-- Exchange the labels `a` and `b`. -/
def swap (a b c : Nat) : Nat := if c = a then b else if c = b then a else c

/-- Exchange the consecutive pairs `a, a+1` and `a+2, a+3`. -/
def swapPairs (a c : Nat) : Nat :=
  if c = a then a+2 else if c = a+1 then a+3 else if c = a+2 then a else
  if c = a+3 then a+1 else c

/-- Compare two strings of bits of `g`, given as a list of pairs of positions. The
result is false only if the first string is smaller where the two first differ. -/
def geBits (g : BitVec w) : List (Nat × Nat) → Bool
  | [] => true
  | (a,b)::bs => if a = b then geBits g bs else
    if g.getLsbD a == g.getLsbD b then geBits g bs else g.getLsbD a

/-- Relabeling the vertices by `s` does not increase the string of bits. -/
def keeps (n k : Nat) (g : BitVec w) (s : Nat → Nat) : Bool :=
  geBits g ((cells n k).map fun c => (n*c.1+c.2, n*s c.1+s c.2))

/-- No swap of neighbors increases the string. The swaps are of two fixed squares, of
the two squares in a pair, of two consecutive pairs, and of two nonsquares. -/
def leads (n k j : Nat) (g : BitVec w) : Bool :=
  (List.range (j-1)).all (fun a => keeps n k g (swap a (a+1))) &&
  (List.range ((k-j)/2)).all (fun i => keeps n k g (swap (j+2*i) (j+2*i+1))) &&
  (List.range ((k-j)/2-1)).all (fun i => keeps n k g (swapPairs (j+2*i))) &&
  (List.range (n-k-1)).all (fun i => keeps n k g (swap (k+i) (k+i+1)))

/-- Write both tests out bit by bit and pass them to the SAT solver. -/
macro "refute_leading" : tactic => `(tactic|
  (dsimp [check, edge, partner, leads, keeps, geBits, cells, swap, swapPairs,
     List.range, List.range.loop, List.all, List.any, List.map, List.flatMap, List.append]
   bv_decide (config := {timeout := 600})))

end E1486.Test
