module

public import Lean

/-! Transfer of the symmetric (ABBA) constraint from an interval to a cycle
using the three labels `⌊3x/m⌋`. Indices are zero-based representatives. -/
@[expose] public section

namespace Erdos160.SymmetricTransfer

/-- The endpoints and middle positions may not both have equal colors. -/
def SymmetricValid (a b c d : α) : Prop := ¬(a = d ∧ b = c)

def IntervalValid (m : Nat) (f : Nat → α) : Prop :=
  ∀ a s : Nat, 0 < s → a+3*s < m →
    SymmetricValid (f a) (f (a+s)) (f (a+2*s)) (f (a+3*s))

def CyclicValid (m : Nat) (f : Nat → α) : Prop :=
  ∀ a s : Nat, a < m → 0 < s → s < m →
    let b := (a+s)%m
    let c := (b+s)%m
    let d := (c+s)%m
    SymmetricValid (f a) (f b) (f c) (f d)

/-- The thirds are half-open, including when `m` is not divisible by three. -/
def tag (m x : Nat) : Fin 3 :=
  if 3*x<m then 0 else if 3*x<2*m then 1 else 2

theorem tag_eq_div {m x : Nat} (hx : x < m) : (tag m x).val = 3*x/m := by
  simp only [tag]
  split
  · symm; exact Nat.div_eq_of_lt (by omega)
  · split
    · symm; exact Nat.div_eq_of_lt_le (by omega : 1*m ≤ 3*x) (by omega)
    · symm; exact Nat.div_eq_of_lt_le (by omega : 2*m ≤ 3*x) (by omega)

private theorem same_third {m x y : Nat} (hx : x<m) (hy : y<m) (eq : tag m x = tag m y) :
    (3*x<m ↔ 3*y<m) ∧ (2*m≤3*x ↔ 2*m≤3*y) ∧ 3*x < 3*y+m ∧ 3*y < 3*x+m := by
  by_cases a : 3*x<m <;> by_cases b : 3*y<m <;> by_cases c : 3*x<2*m <;> by_cases d : 3*y<2*m <;>
    simp [tag,a,b,c,d] at eq <;> omega

abbrev Next (m s x y : Nat) := x+s=y ∨ x+s=m+y

private theorem next_mod {m s x : Nat} (hx : x<m) (hs : s<m) : Next m s x ((x+s)%m) := by
  by_cases small : x+s<m
  · left; exact (Nat.mod_eq_of_lt small).symm
  · right
    rw [Nat.mod_eq_sub_mod (by omega : m≤x+s), Nat.mod_eq_of_lt (by omega)]
    omega

private theorem reverse_step {m s x y : Nat} (hs : s<m) (h : Next m s x y) :
    Next m (m-s) y x := by
  rcases h with h|h
  · right; omega
  · left; omega

/-- At a step at most half the modulus, equal tags in both symmetric pairs
force the entire progression to lift without wrapping. -/
theorem symmetric_lifts {m s a b c d : Nat} (small : 2*s≤m)
    (ha : a<m) (hb : b<m) (hc : c<m) (hd : d<m)
    (ab : Next m s a b) (bc : Next m s b c) (cd : Next m s c d)
    (adEq : tag m a = tag m d) (bcEq : tag m b = tag m c) :
    a+s=b ∧ b+s=c ∧ c+s=d := by
  obtain ⟨adL,adR,adB,daB⟩ := same_third ha hd adEq
  obtain ⟨bcL,bcR,bcB,cbB⟩ := same_third hb hc bcEq
  rcases ab with ab|ab <;> rcases bc with bc|bc <;> rcases cd with cd|cd <;> omega

def refined (m : Nat) (f : Nat → α) (x : Nat) : α × Fin 3 := (f x, tag m x)

private theorem small_valid {m s a b c d : Nat} {f : Nat → α} (hf : IntervalValid m f)
    (hs : 0<s) (small : 2*s≤m) (ha : a<m) (hb : b<m) (hc : c<m) (hd : d<m)
    (ab : Next m s a b) (bc : Next m s b c) (cd : Next m s c d) :
    SymmetricValid (refined m f a) (refined m f b) (refined m f c) (refined m f d) := by
  rintro ⟨adEq, bcEq⟩
  obtain ⟨u,v,w⟩ := symmetric_lifts small ha hb hc hd ab bc cd
    (congrArg Prod.snd adEq) (congrArg Prod.snd bcEq)
  have e := hf a s hs (by omega)
  rw [u, show a+2*s=c by omega, show a+3*s=d by omega] at e
  exact e ⟨congrArg Prod.fst adEq, congrArg Prod.fst bcEq⟩

theorem refined_valid {m : Nat} {f : Nat → α} (hf : IntervalValid m f) :
    CyclicValid m (refined m f) := by
  intro a s ha hs hm
  let b := (a+s)%m
  let c := (b+s)%m
  let d := (c+s)%m
  have hb : b<m := Nat.mod_lt _ (by omega)
  have hc : c<m := Nat.mod_lt _ (by omega)
  have hd : d<m := Nat.mod_lt _ (by omega)
  have ab : Next m s a b := next_mod ha hm
  have bc : Next m s b c := next_mod hb hm
  have cd : Next m s c d := next_mod hc hm
  by_cases small : 2*s≤m
  · exact small_valid hf hs small ha hb hc hd ab bc cd
  · have rev := small_valid hf (by omega : 0<m-s) (by omega) hd hc hb ha
      (reverse_step hm cd) (reverse_step hm bc) (reverse_step hm ab)
    exact fun ⟨ad,bc⟩ => rev ⟨ad.symm,bc.symm⟩

private def pack (z : Fin k × Fin 3) : Fin (3*k) :=
  ⟨3*z.1.val+z.2.val, by have := z.1.isLt; have := z.2.isLt; omega⟩

private theorem pack_injective {x y : Fin k × Fin 3} (e : pack x = pack y) : x=y := by
  have eq := congrArg Fin.val e
  change 3*x.1.val+x.2.val=3*y.1.val+y.2.val at eq
  have hx := x.2.isLt
  have hy := y.2.isLt
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

/-- Every interval `k`-coloring avoiding ABBA extends to a coloring of the
cycle of the same length with at most `3*k` colors, for every modulus. -/
theorem interval_to_cyclic {m k : Nat} (f : Nat → Fin k) (hf : IntervalValid m f) :
    ∃ g : Nat → Fin (3*k), CyclicValid m g := by
  refine ⟨fun x => pack (refined m f x), ?_⟩
  intro a s ha hs hm
  have h := refined_valid hf a s ha hs hm
  dsimp only at h ⊢
  unfold SymmetricValid at h ⊢
  rintro ⟨ad,bc⟩
  exact h ⟨pack_injective ad,pack_injective bc⟩

end Erdos160.SymmetricTransfer
#print axioms Erdos160.SymmetricTransfer.interval_to_cyclic
