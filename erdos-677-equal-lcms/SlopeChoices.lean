module

public import Init

@[expose] public section

namespace Erdos677

/-- Data proposed for a slab `L ≤ X < 2L`. A user of the generator checks
the modular inverse and both integer inequalities before applying the bound. -/
structure SlopeChoice where
  p : Nat
  q : Nat
  z : Nat
  E : Nat
  deriving Repr, Inhabited

-- Integer Newton iteration, initialized from the bit length of the radicand.
def rootNewton (k value : Nat) : Nat → Nat → Nat
  | 0, x => x
  | fuel+1, x =>
    let y := ((k-1)*x + value / x^(k-1)) / k
    if x ≤ y then x else rootNewton k value fuel y

-- Return the most recent convergent with denominator ≤ L, together with the
-- preceding denominator. The latter gives an inverse, up to a sign.
def convergent (L : Nat) : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, _, _, _, p, qPrev, q => (p, q, qPrev)
  | fuel+1, a, b, pPrev, p, qPrev, q =>
    if b = 0 then (p, q, qPrev) else
      let c := a / b
      let qNext := c*q + qPrev
      if L < qNext then (p, q, qPrev) else
        convergent L fuel b (a % b) p (c*p+pPrev) q qNext

def chooseError (k u v L p q : Nat) : Nat → Nat → Nat
  | 0, E => E
  | fuel+1, E =>
    if (p*L-E)^k * v * L^2 ≤ (q*L)^k * u * (L^2-35) ∧
        (q*L)^k * u * L^2 ≤ (p*L+E)^k * v * (L^2-35) then E
    else chooseError k u v L p q fuel (2*E)

/-- Compute a rational slope, its modular inverse, and a determinant-error
bound for the centered products of lengths 5 and 6. All operations use natural
numbers; validity is checked by the calling proof. -/
def slopeChoice (k u v L : Nat) : SlopeChoice :=
  let Q := 4 * L^2
  let value := u * Q^k / v
  let start := 2 ^ ((value.log2 + k) / k)
  let a := rootNewton k value (value.log2+3) start
  let (p, q, prev) := convergent L (2*Q.log2+5) a Q 0 1 1 0
  let z := if p*prev % q = 1 % q then prev % q else (q - prev % q) % q
  let E := chooseError k u v L p q ((p*L + q*L*u+4).log2 + 5) 1
  ⟨p, q, z, E⟩

end Erdos677
