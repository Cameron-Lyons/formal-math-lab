import Matchsticks.Certificate

/-! Each natural number in this module encodes a set of frontier states.
Index `s` is itself a 15-bit mask of open pairs of horizontal levels.
Horizontal changes erase selected bits of a state. Vertical changes add
the row pairs on the new boundary, subject to the rectangle test.
The lemmas below let Lean verify these changes for many states at once. -/
namespace Matchsticks.BitSets

/-- Broadcast membership to smaller indices separated by submasks of `mask`. -/
def spreadR : (n mask stride A : Nat) → Nat
  | 0, _, _, A => A
  | n+1, mask, stride, A => spreadR n (mask / 2) (2*stride)
      (if mask % 2 = 1 then A ||| (A >>> stride) else A)

/-- Broadcast membership to larger indices separated by submasks of `mask`. -/
def spreadL : (n mask stride A : Nat) → Nat
  | 0, _, _, A => A
  | n+1, mask, stride, A => spreadL n (mask / 2) (2*stride)
      (if mask % 2 = 1 then A ||| (A <<< stride) else A)

private theorem halveSub {u mask : Nat} (h : u &&& mask = u) :
    (u/2) &&& (mask/2) = u/2 := by rw [← Nat.and_div_two, h]

private theorem lowBit {u mask : Nat} (h : u &&& mask = u) (hu : u % 2 = 1) :
    mask % 2 = 1 := (Nat.and_mod_two_eq_one.mp (h ▸ hu)).2

private theorem divideBound {u n : Nat} (h : u < 2^(n+1)) : u/2 < 2^n := by
  rw [Nat.pow_succ] at h
  omega

private theorem strideParts (stride u : Nat) :
    stride * u = 2*stride*(u/2) + stride*(u % 2) := by
  calc stride*u = stride*(2*(u/2) + u%2) := congrArg (stride * ·) (by omega)
       _ = _ := by simp only [Nat.mul_add]; rw [← Nat.mul_assoc, Nat.mul_comm stride 2]

theorem spreadR_mem {n mask stride A u x : Nat} (sub : u &&& mask = u)
    (bound : u < 2^n) (hit : A.testBit (x+stride*u) = true) :
    (spreadR n mask stride A).testBit x = true := by
  induction n generalizing mask stride A u with
  | zero =>
    have hu : u = 0 := by simpa using bound
    simpa [hu, spreadR] using hit
  | succ n ih =>
    apply ih (halveSub sub) (divideBound bound)
    rw [strideParts] at hit
    by_cases hu : u % 2 = 1
    · simp only [lowBit sub hu, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftRight,
        Bool.or_eq_true]
      right
      simpa [hu, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hit
    · have he : u%2 = 0 := by omega
      have hh : A.testBit (x+2*stride*(u/2)) = true := by simpa [he] using hit
      split <;> simp [hh]

theorem spreadL_mem {n mask stride A u x : Nat} (sub : u &&& mask = u)
    (bound : u < 2^n) (hit : A.testBit x = true) :
    (spreadL n mask stride A).testBit (x+stride*u) = true := by
  induction n generalizing mask stride A u x with
  | zero =>
    have hu : u = 0 := by simpa using bound
    simpa [hu, spreadL] using hit
  | succ n ih =>
    rw [strideParts]
    have heq : x+(2*stride*(u/2)+stride*(u%2)) = (x+stride*(u%2))+2*stride*(u/2) := by omega
    rw [heq]
    apply ih (halveSub sub) (divideBound bound)
    by_cases hu : u%2 = 1
    · simp [lowBit sub hu, hu, Nat.testBit_shiftLeft, hit]
    · have he : u%2 = 0 := by omega
      split <;> simp [he, hit]

def complement (mask : Nat) : Nat := 32767 ^^^ mask

def allowed (mask : Nat) : Nat := spreadL 15 mask 1 1

def horizSource (k : Nat) (h : HMask) : Nat :=
  spreadR 15 (complement (hPairs h)) 1 (potentialSet k) &&& allowed (hPairs h)

def vertSource (k : Nat) (v : VMask) : Nat :=
  middleSet k &&& allowed (complement (vPairs v))

private theorem or_as_sum {a b : Nat} (ha : a < 2^15) (hb : b < 2^15)
    (h : a &&& b = 0) : a ||| b = a+b := by
  let x := BitVec.ofNat 15 a
  let y := BitVec.ofNat 15 b
  have hxy : x &&& y = 0#15 := by simp only [x,y, ← BitVec.ofNat_and, h]
  have hsum := BitVec.toNat_add_of_and_eq_zero hxy
  rw [BitVec.add_eq_or_of_and_eq_zero x y hxy, BitVec.toNat_or] at hsum
  simpa only [x,y, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hsum

private theorem andComplement {s : Nat} (hs : s < 2^15) (m : Nat) :
    s &&& complement m = s ^^^ (s &&& m) := by
  rw [complement, Nat.and_xor_distrib_left]
  rw [show s &&& 32767 = s from Nat.and_two_pow_sub_one_of_lt_two_pow hs]

private theorem maskSplit {s m : Nat} (hs : s < 2^15) :
    (s &&& m) + (s &&& complement m) = s := by
  rw [← or_as_sum (Nat.lt_of_le_of_lt Nat.and_le_left hs) (Nat.lt_of_le_of_lt Nat.and_le_left hs)]
  · rw [andComplement hs]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h₁ : s.testBit i <;> cases h₂ : m.testBit i <;> simp [h₁,h₂]
  · rw [andComplement hs]
    apply Nat.eq_of_testBit_eq
    intro i
    cases h₁ : s.testBit i <;> cases h₂ : m.testBit i <;> simp [h₁,h₂]

private theorem allowedOfSub {u m : Nat} (sub : u &&& m = u) (bound : u < 2^15) :
    (allowed m).testBit u = true := by
  have one : (1:Nat).testBit 0 = true := rfl
  simpa [allowed] using (spreadL_mem (stride:=1) sub bound one)

theorem horiz_mem (s k : Nat) (h : HMask) (hs : s < 32768)
    (hit : (potentialSet k).testBit s = true) :
    (horizSource k h).testBit (s &&& hPairs h) = true := by
  let m := hPairs h
  let u := s &&& complement m
  let t := s &&& m
  have hu : u &&& complement m = u := by simp only [u, Nat.and_assoc, Nat.and_self]
  have ht : t &&& m = t := by simp only [t, Nat.and_assoc, Nat.and_self]
  have ub : u < 2^15 := Nat.lt_of_le_of_lt Nat.and_le_left hs
  have tb : t < 2^15 := Nat.lt_of_le_of_lt Nat.and_le_left hs
  have good : (potentialSet k).testBit (t+1*u) = true := by
    simpa only [Nat.one_mul, t, u, maskSplit hs] using hit
  simp only [horizSource, Nat.testBit_and, Bool.and_eq_true]
  exact ⟨spreadR_mem hu ub good, allowedOfSub ht tb⟩

theorem vert_mem (t k : Nat) (v : VMask) (ht : t < 32768) (ok : t &&& vPairs v = 0)
    (hit : (middleSet k).testBit t = true) :
    (vertSource k v).testBit t = true ∧ (t ||| vPairs v) = t+vPairs v ∧ (t ||| vPairs v)<32768 := by
  have sub : t &&& complement (vPairs v) = t := by rw [andComplement ht, ok, Nat.xor_zero]
  simp only [vertSource, Nat.testBit_and, Bool.and_eq_true]
  exact ⟨⟨hit, allowedOfSub sub ht⟩,
    or_as_sum ht (vPairs_bound v) ok, Nat.or_lt_two_pow ht (vPairs_bound v)⟩

end Matchsticks.BitSets
