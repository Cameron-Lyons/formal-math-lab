import Std.Tactic.BVDecide

namespace E1486.Simple.Finite

abbrev Mask := BitVec 15
abbrev G := BitVec 225

/-- The 15 bits in row a record the arrows leaving vertex a. -/
def row (g : G) (a : Nat) : Mask := g.extractLsb' (15*a) 15

def partner (j a : Nat) : Nat := if a < j then a else if (a-j)%2=0 then a+1 else a-1

def one (j a : Nat) : Mask := 1 <<< partner j a

/-- The first k vertices are squares: the first j are fixed by squaring,
and the rest form consecutive pairs. The graph g and its transpose t give
outgoing and incoming neighbors as bit sets; `&&&` takes their intersection. -/
def check (k j : Nat) (g t : G) : Bool :=
  (List.range 15).all fun a =>
    -- 1. The incoming and outgoing representations describe the same arrows.
    (List.range 15).all (fun b => g.getLsbD (15*a+b) == t.getLsbD (15*b+a)) &&
    -- 2. Every vertex has an incoming arrow from a square (one of the first k bits).
    (row t a &&& (BitVec.ofNat 15 (2^k-1))) != 0 &&
    -- 3. The middle vertices on a → i → a are exactly the prescribed partner
    -- when a is a square, and there are none when a is a nonsquare.
    (row t a &&& row g a) == (if a<k then one j a else 0) &&
    -- 4. Every vertex reaches every square q by a two-step route.
    (List.range k).all (fun q => (row g a &&& row t q) != 0) &&
    -- 5. Distinct middle vertices a,b cannot share both a predecessor x and
    -- a successor y: that would give two routes x → a → y and x → b → y.
    (List.range a).all (fun b => (row t a &&& row t b) == 0 || (row g a &&& row g b) == 0)

/-- Compare the graph and a relabeling, most significant coordinate first. -/
def geBits (g : G) : List (Nat × Nat) → Bool
  | [] => true
  | (a,b)::bs => if a == b then geBits g bs else
    if g.getLsbD a == g.getLsbD b then geBits g bs else g.getLsbD a

def nonSq (k : Nat) (a : Nat) :=
  (List.range k).map (fun q => (15*q+a,15*q+a+1)) ++
  (List.range k).map (fun q => (15*a+q,15*(a+1)+q))

def swap (a b c : Nat) := if c==a then b else if c==b then a else c

def sqBits (k : Nat) (p : Nat → Nat) :=
  (List.range k).flatMap fun x => (List.range k).map fun y => (15*x+y,15*(p x)+p y)

def ordered (k j : Nat) (g : G) : Bool :=
  (List.range (14-k)).all (fun i => geBits g (nonSq k (k+i))) &&
  (List.range k).all fun b => (List.range b).all fun a =>
    if b<j || (j≤a && (a-j)%2==0 && b==a+1) then geBits g (sqBits k (swap a b))
    else if j≤a && (a-j)%2==0 && (b-j)%2==0 then
      geBits g (sqBits k (fun x => swap a b (swap (a+1) (b+1) x)))
    else true

end E1486.Simple.Finite
