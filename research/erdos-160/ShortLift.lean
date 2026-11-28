module

public import Lean

/-! A dyadic boundary label for lifting short cyclic progressions. -/
@[expose] public section

namespace Erdos160.ShortLift

/-- Record parity and the dyadic bands of the two positive boundary distances. -/
def tag (m x : Nat) : Nat × Nat × Nat := (x % 2, (x+1).log2, (m-x).log2)

private theorem same_band {a b : Nat} (hb : 0 < b) (h : a.log2 = b.log2) : a < 2*b := by
  have lo := Nat.log2_self_le (Nat.ne_of_gt hb)
  have hi := Nat.lt_log2_self (n:=a)
  rw [h, Nat.pow_succ] at hi
  omega

/-- Reflecting an equally tagged point about its mate stays in the interval. -/
private theorem reflect_bounds {m x y : Nat} (hy : y < m) (eq : tag m x = tag m y) :
    x ≤ 2*y ∧ 2*y < m+x := by
  have left := same_band (a:=x+1) (b:=y+1) (by omega) (congrArg (fun t => t.2.1) eq)
  have right := same_band (a:=m-x) (show 0<m-y by omega) (congrArg (fun t => t.2.2) eq)
  omega

private theorem one_carry {m u : Nat} (bound : u < 2*m) : u = u%m ∨ u = u%m+m := by
  by_cases h : u<m
  · exact Or.inl (Nat.mod_eq_of_lt h).symm
  · right
    rw [Nat.mod_eq_sub_mod (by omega : m≤u), Nat.mod_eq_of_lt (by omega)]
    omega

/-- A cyclic three-term progression modulo an odd modulus lifts to the ordinary
integer progression of its representatives as soon as any two labels match. -/
theorem lift_three {m x y z : Nat} (odd : m%2=1) (hx : x<m) (hy : y<m) (hz : z<m)
    (ap : (x+z)%m=(2*y)%m)
    (pair : tag m x=tag m y ∨ tag m y=tag m z ∨ tag m x=tag m z) : x+z=2*y := by
  have a := one_carry (m:=m) (u:=x+z) (by omega)
  have b := one_carry (m:=m) (u:=2*y) (by omega)
  rcases pair with eq | eq | eq
  · have := reflect_bounds hy eq
    omega
  · have := reflect_bounds hy eq.symm
    omega
  · have p : x%2=z%2 := congrArg Prod.fst eq
    omega

/-- At most two labels on a cyclic four-term progression force both ordinary second
differences to vanish, including when the representatives are decreasing. -/
theorem lift_four {m a b c d : Nat} (odd : m%2=1) (ha : a<m) (hb : b<m) (hc : c<m) (hd : d<m)
    (abc : (a+c)%m=(2*b)%m) (bcd : (b+d)%m=(2*c)%m)
    (two : ∃ p q, ∀ x ∈ [a,b,c,d], tag m x=p ∨ tag m x=q) : a+c=2*b ∧ b+d=2*c := by
  obtain ⟨p,q,h⟩ := two
  have A := h a (by simp)
  have B := h b (by simp)
  have C := h c (by simp)
  have D := h d (by simp)
  exact ⟨lift_three odd ha hb hc abc (by grind), lift_three odd hb hc hd bcd (by grind)⟩

end Erdos160.ShortLift
#print axioms Erdos160.ShortLift.lift_three
#print axioms Erdos160.ShortLift.lift_four
