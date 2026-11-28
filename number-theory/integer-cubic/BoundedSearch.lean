import Std

/-!
Check which divisors z of 2 − x³ give a square (2 − x³)/z − z in F₁₃[T].
Polynomial coefficients are stored in increasing order of degree.
-/
namespace BoundedSearch

abbrev Poly := Array Nat

def trim (f : Poly) : Poly := (f.toList.reverse.dropWhile (· == 0)).reverse.toArray

def sub (f g : Poly) : Poly := trim <| (Array.range (max f.size g.size)).map
  fun i => (f[i]?.getD 0 + 13 - (g[i]?.getD 0)) % 13

def scale (a : Nat) (f : Poly) : Poly := f.map (fun c => a * c % 13)

def mul (f g : Poly) : Poly := Id.run do
  if f.isEmpty || g.isEmpty then return #[]
  let mut h := Array.replicate (f.size + g.size - 1) 0
  for i in [:f.size] do
    for j in [:g.size] do
      h := h.set! (i + j) ((h[i + j]! + f[i]! * g[j]!) % 13)
  return h

def inv (a : Nat) := a ^ 11 % 13

def monic (f : Poly) := scale (inv (f.back?.getD 0)) f

/-- Quotient and remainder for a monic divisor. -/
def divMod (f g : Poly) : Poly × Poly := Id.run do
  let mut r := f
  let mut q := Array.replicate (f.size + 1 - g.size) 0
  for j in [:q.size] do
    let i := q.size - 1 - j
    let c := r[i + g.size - 1]!
    q := q.set! i c
    for k in [:g.size] do
      r := r.set! (i + k) ((r[i + k]! + 13 - c * g[k]! % 13) % 13)
  return (trim q, trim (r.extract 0 (g.size - 1)))

partial def gcd (f g : Poly) : Poly :=
  if g.isEmpty then monic f else gcd g (divMod f (monic g)).2

partial def powMod (a : Poly) (n : Nat) (f : Poly) : Poly :=
  if n == 0 then #[1] else
    let b := powMod a (n / 2) f
    let s := (divMod (mul b b) f).2
    if n % 2 == 0 then s else (divMod (mul s a) f).2

def decode (n code : Nat) : Poly :=
  (Array.range n).map fun i => code / 13 ^ i % 13

/-- T^(13^d)-T contains every monic irreducible of degree dividing d exactly once.
At the first nontrivial gcd, equality with f means it is a product of
distinct degree-d factors.
By the Chinese remainder theorem there is an a that is 1 modulo one factor
and 0 modulo another. Trying quadratic characters speeds up the search for a split. -/
def properFactor (f : Poly) : Option Poly := Id.run do
  let t := #[0, 1]
  let mut u := t
  for d in [1:(f.size - 1) / 2 + 1] do
    u := powMod u 13 f
    let g := gcd f (sub u t)
    if g.size > 1 then
      if g != f then return some g
      for code in [13:13 ^ (f.size - 1)] do
        let a := trim (decode (f.size - 1) code)
        let h := gcd f (sub (powMod a ((13 ^ d - 1) / 2) f) #[1])
        if h.size > 1 && h != f then return some h
  return none

partial def factors (f : Poly) : List Poly :=
  if f.size ≤ 1 then []
  else match properFactor f with
    | none => [f]
    | some g => factors g ++ factors (divMod f g).1

def divisors (f : Poly) : List Poly :=
  (factors (monic f)).foldl (fun ds q => ds ++ ds.map (mul q)) [#[1]]

def squareResidue (a : Nat) : Bool := [0, 1, 3, 4, 9, 10, 12].contains a

/-- Squares have square leading coefficients and even factor multiplicities. -/
def isSquare (f : Poly) : Bool := Id.run do
  if f.isEmpty then return true
  if f.size % 2 == 0 || !squareResidue f.back! then return false
  for t in [:13] do
    if !squareResidue (f.foldr (fun c v => (c + t * v) % 13) 0) then return false
  let fs := factors (monic f)
  return fs.all (fun g => fs.count g % 2 == 0)

/-- Translation removes the next-to-leading term. Scaling T normalizes the leading term. -/
def searchDegree (degree : Nat) : Nat × Nat := Id.run do
  let mut candidates := 0
  let mut hits := 0
  for a in [1:13] do
    if (List.range 12 |>.all fun j => a ≤ a * (j + 1) ^ degree % 13) then
      for code in [:13 ^ (degree - 1)] do
        let x := ((decode (degree - 1) code).push 0).push a
        candidates := candidates + 1
        let f := sub #[2] (mul (mul x x) x)
        -- Each possible z is b*g, with g monic and b nonzero.
        for g in divisors f do
          let h := (divMod f g).1
          for b in [1:13] do
            if isSquare (sub (scale (inv b) h) (scale b g)) then hits := hits + 1
  return (candidates, hits)

end BoundedSearch

def main : IO Unit := do
  for d in [1:6] do
    let (candidates, hits) := BoundedSearch.searchDegree d
    IO.println s!"Degree {d} | {candidates} normalized polynomials | {hits} square differences"
    unless hits == 0 do throw (IO.userError "unexpected polynomial solution")
