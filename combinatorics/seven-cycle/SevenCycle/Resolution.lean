import SevenCycle.Basic

namespace SevenCycle.Cert

/-- Bit `3 * edge + k` requires color `k` on that edge. -/
def bit (edge k : Nat) : Nat := 2 ^ (3 * edge + k)

def index (a b : Fin 10) : Nat := 10 * min a.val b.val + max a.val b.val

def readColor (c : Coloring 10) (edge : Nat) : Color :=
  c.edge (Fin.ofNat 10 (edge / 10)) (Fin.ofNat 10 (edge % 10))

private theorem read_index (c : Coloring 10) (a b : Fin 10) :
    readColor c (index a b) = c.edge a b := by
  have h : ∀ x y : Fin 10, x ≤ y →
      Fin.ofNat 10 (index x y / 10) = x ∧ Fin.ofNat 10 (index x y % 10) = y := by decide
  by_cases hab : a ≤ b
  · rcases h a b hab with ⟨h₁, h₂⟩
    simp [readColor, h₁, h₂]
  · have hi : index a b = index b a := by simp [index, Nat.min_comm, Nat.max_comm]
    rcases h b a (by omega) with ⟨h₁, h₂⟩
    simp [hi, readColor, h₁, h₂, c.symm b a]

/-- All the edge-color requirements encoded by `m` hold in `c`. -/
def Covers (c : Coloring 10) (m : Nat) : Prop :=
  ∀ (edge : Nat) (k : Color), m.testBit (3 * edge + k.val) = true → readColor c edge = k

/-- Every coloring extending this partial assignment has a good seven-cycle. -/
def Valid (m : Nat) : Prop := ∀ c : Coloring 10, Covers c m → HasGoodSeven c

private theorem covers_bit {c : Coloring 10} {e : Nat} {k : Color} (h : readColor c e = k) :
    Covers c (bit e k.val) := by
  intro f t ht
  simp only [bit, Nat.testBit_two_pow, decide_eq_true_eq] at ht
  have hef : e = f := by omega
  have hkt : k = t := Fin.ext (by omega)
  simpa [← hef, ← hkt] using h

private theorem covers_union {c : Coloring 10} {x y : Nat} (hx : Covers c x) (hy : Covers c y) :
    Covers c (x ||| y) := by
  intro e k h
  rw [Nat.testBit_or, Bool.or_eq_true] at h
  exact h.elim (hx e k) (hy e k)

private theorem covers_sub {c : Coloring 10} {m s : Nat} (h : s &&& m = s) (hm : Covers c m) :
    Covers c s := by
  intro e k hk
  have hb := congrArg (fun x : Nat => x.testBit (3 * e + k.val)) h
  simp only [Nat.testBit_and, hk, Bool.true_and] at hb
  exact hm e k hb

def splitOK (e p x y z : Nat) : Bool :=
  (x &&& (p ||| bit e 0) == x) && (y &&& (p ||| bit e 1) == y) && (z &&& (p ||| bit e 2) == z)

/-- Resolve the three possible colors of one edge. The three children can
use different subsets of the assumptions available to them. -/
theorem split (edge parent x y z : Nat) (hx : Valid x) (hy : Valid y) (hz : Valid z)
    (ok : splitOK edge parent x y z = true) : Valid parent := by
  simp only [splitOK, Bool.and_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨h₀, h₁⟩, h₂⟩ := ok
  intro c hp
  obtain he | he | he := (by decide : ∀ k : Color, k = 0 ∨ k = 1 ∨ k = 2) (readColor c edge)
  · exact hx c (covers_sub h₀ (covers_union hp (covers_bit he)))
  · exact hy c (covers_sub h₁ (covers_union hp (covers_bit he)))
  · exact hz c (covers_sub h₂ (covers_union hp (covers_bit he)))

private def requirement (a b : Fin 10) (k : Color) := bit (index a b) k.val

def leafMask (a b c d e f g : Fin 10) (u v w x y z t : Color) : Nat :=
  requirement a b u ||| requirement b c v ||| requirement c d w ||| requirement d e x |||
  requirement e f y ||| requirement f g z ||| requirement g a t

def leafOK (a b c d e f g : Fin 10) (u v w x y z t : Color) (m : Nat) : Bool :=
  (leafMask a b c d e f g u v w x y z t == m) && decide [a,b,c,d,e,f,g].Nodup &&
  decide (jump u v + (jump v w + (jump w x + (jump x y + (jump y z + (jump z t + jump t u))))) ≤ 2)

private theorem covers_edge (c : Coloring 10) (m : Nat) (hm : Covers c m) (a b : Fin 10)
    (k : Color) (h : m.testBit (3 * index a b + k.val) = true) : c.edge a b = k := by
  simpa [read_index] using hm (index a b) k h

/-- A leaf supplies its seven distinct vertices and their cyclic edge colors. -/
theorem leaf (a b c d e f g : Fin 10) (u v w x y z t : Color) (m : Nat)
    (ok : leafOK a b c d e f g u v w x y z t m = true) : Valid m := by
  simp only [leafOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  obtain ⟨⟨rfl, hdistinct⟩, hchanges⟩ := ok
  intro col hm
  have get := covers_edge col _ hm
  refine ⟨[a,b,c,d,e,f,g], rfl, hdistinct, ?_⟩
  change jump _ _ + (jump _ _ + (jump _ _ + (jump _ _ + (jump _ _ + (jump _ _ + (jump _ _ + 0)))))) ≤ 2
  have ab := get a b u (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have bc := get b c v (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have cd := get c d w (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have de := get d e x (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have ef := get e f y (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have fg := get f g z (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  have ga := get g a t (by simp [leafMask, requirement, bit, Nat.testBit_two_pow])
  simpa only [ab, bc, cd, de, ef, fg, ga, Nat.add_zero] using! hchanges

/-- Edges 01,02,03,04 are red. The six edges among the leaves have the
little-endian base-three digits of `s`, in triangular order. -/
def seedMask (s : Nat) : Nat :=
  bit 1 0 ||| bit 2 0 ||| bit 3 0 ||| bit 4 0 |||
  bit 12 (s % 3) ||| bit 13 (s / 3 % 3) ||| bit 23 (s / 9 % 3) |||
  bit 14 (s / 27 % 3) ||| bit 24 (s / 81 % 3) ||| bit 34 (s / 243 % 3)

/-- Build a covered seed from its ten edge colors. -/
theorem covers_seed (c : Coloring 10) (s : Nat)
    (h₁ : c.edge 0 1 = 0) (h₂ : c.edge 0 2 = 0) (h₃ : c.edge 0 3 = 0) (h₄ : c.edge 0 4 = 0)
    (d₁ : s % 3 = (c.edge 1 2).val) (d₂ : s / 3 % 3 = (c.edge 1 3).val)
    (d₃ : s / 9 % 3 = (c.edge 2 3).val) (d₄ : s / 27 % 3 = (c.edge 1 4).val)
    (d₅ : s / 81 % 3 = (c.edge 2 4).val) (d₆ : s / 243 % 3 = (c.edge 3 4).val) :
    Covers c (seedMask s) := by
  unfold seedMask
  rw [d₁, d₂, d₃, d₄, d₅, d₆]
  repeat' apply covers_union
  all_goals first | apply covers_bit (k := 0) | apply covers_bit
  all_goals first | exact h₁ | exact h₂ | exact h₃ | exact h₄ | rfl

end SevenCycle.Cert
