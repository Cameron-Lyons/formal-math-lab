module

public import CyclicTransfer

/-! Multiplication, powering, and restriction of cyclic progression colorings.
The two digit projections work even when the factor moduli have common factors. -/
@[expose] public section

namespace Erdos160.CyclicTransfer

private theorem three_of_projection (p : β → α) {a b c d : β}
    (h : Three (p a) (p b) (p c) (p d)) : Three a b c d := by
  unfold Three at *
  grind

/-- Read the low digit modulo m and the high digit modulo n. -/
def digitProduct (m : Nat) (f : Nat → α) (g : Nat → β) (x : Nat) : α × β :=
  (f (x%m), g (x/m))

theorem cyclic_product {m n : Nat} (hm : 0<m) (_hn : 0<n)
    {f : Nat → α} {g : Nat → β} (hf : CyclicValid m f) (hg : CyclicValid n g) :
    CyclicValid (m*n) (digitProduct m f g) := by
  intro a s ha hs hsm
  let b := (a+s)%(m*n)
  let c := (b+s)%(m*n)
  let d := (c+s)%(m*n)
  change Three (digitProduct m f g a) (digitProduct m f g b)
    (digitProduct m f g c) (digitProduct m f g d)
  by_cases exactStep : s%m=0
  · have eq : m*(s/m)=s := by simpa [exactStep] using Nat.div_add_mod s m
    have positive : 0 < s/m := by
      by_cases h : s/m=0
      · rw [h, Nat.mul_zero] at eq
        omega
      · exact Nat.pos_of_ne_zero h
    have project (u : Nat) : ((u+s)%(m*n))/m = (u/m+s/m)%n := by
      rw [Nat.mod_mul_right_div_self]
      have e : (u+s)/m=u/m+s/m := by
        conv => lhs; rw [← eq]
        exact Nat.add_mul_div_left _ _ hm
      rw [e]
    apply three_of_projection Prod.snd
    change Three (g (a/m)) (g (b/m)) (g (c/m)) (g (d/m))
    have hb : b/m = (a/m+s/m)%n := project a
    have hc : c/m = (b/m+s/m)%n := project b
    have hd : d/m = (c/m+s/m)%n := project c
    rw [hd,hc,hb]
    exact hg (a/m) (s/m) ((Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using ha))
      positive ((Nat.div_lt_iff_lt_mul hm).2 (by simpa [Nat.mul_comm] using hsm))
  · have project (u : Nat) : ((u+s)%(m*n))%m = (u%m+s%m)%m := by
      rw [Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right _ _), Nat.add_mod_mod, Nat.mod_add_mod]
    apply three_of_projection Prod.fst
    change Three (f (a%m)) (f (b%m)) (f (c%m)) (f (d%m))
    have hb : b%m = (a%m+s%m)%m := project a
    have hc : c%m = (b%m+s%m)%m := project b
    have hd : d%m = (c%m+s%m)%m := project c
    rw [hd,hc,hb]
    exact hf (a%m) (s%m) (Nat.mod_lt _ hm) (by omega) (Nat.mod_lt _ hm)

/-- Restriction to any initial interval of length at most the modulus. -/
theorem restrict_cyclic {m N : Nat} {f : Nat → α} (hf : CyclicValid m f) (hm : N≤m) :
    IntervalValid N f := by
  intro a s hs hbound
  have h := hf a s (by omega) hs (by omega)
  dsimp at h
  simp only [Nat.mod_eq_of_lt (by omega : a+s<m),
    Nat.mod_eq_of_lt (by omega : a+s+s<m), Nat.mod_eq_of_lt (by omega : a+s+s+s<m)] at h
  simpa only [show a+s+s=a+2*s by omega, show a+2*s+s=a+3*s by omega] using h

private def packPair (z : Fin k × Fin l) : Fin (k*l) :=
  ⟨z.1.val*l+z.2.val, by
    have h := Nat.add_lt_add_left z.2.isLt (z.1.val*l)
    have bound := Nat.mul_le_mul_right l (show z.1.val+1 ≤ k from z.1.isLt)
    rw [Nat.succ_mul] at bound
    exact Nat.lt_of_lt_of_le h bound⟩

private theorem packPair_injective {x y : Fin k × Fin l} (h : packPair x = packPair y) : x=y := by
  rcases x with ⟨i,j⟩
  rcases y with ⟨i',j'⟩
  have hl : 0<l := Nat.zero_lt_of_lt j.isLt
  have eq : i.val*l+j.val = i'.val*l+j'.val := congrArg Fin.val h
  have quotient (a : Fin k) (b : Fin l) : (a.val*l+b.val)/l = a.val := by
    rw [Nat.mul_comm a.val l, Nat.mul_add_div hl, Nat.div_eq_of_lt b.isLt, Nat.add_zero]
  have ei : i=i' := Fin.ext (by simpa only [quotient] using congrArg (· / l) eq)
  have ej : j=j' := Fin.ext (by simpa [ei] using eq)
  simp [ei,ej]

/-- Finite palettes multiply under cyclic products. -/
theorem cyclic_product_fin {m n k l : Nat} (hm : 0<m) (hn : 0<n)
    (f : Nat → Fin k) (g : Nat → Fin l) (hf : CyclicValid m f) (hg : CyclicValid n g) :
    ∃ u : Nat → Fin (k*l), CyclicValid (m*n) u := by
  refine ⟨fun x => packPair (digitProduct m f g x), ?_⟩
  intro a s ha hs hsm
  have h := cyclic_product hm hn hf hg a s ha hs hsm
  dsimp at h ⊢
  unfold Three at h ⊢
  grind [packPair_injective]

/-- An r-coloring modulo m supplies an r^t-coloring modulo m^t. -/
theorem cyclic_power {m k : Nat} (hm : 0<m) (f : Nat → Fin k) (hf : CyclicValid m f) (t : Nat) :
    ∃ g : Nat → Fin (k^t), CyclicValid (m^t) g := by
  induction t with
  | zero =>
    refine ⟨fun _ => ⟨0, by simp⟩, ?_⟩
    intro a s ha hs hsm
    simp at hsm
    omega
  | succ t ih =>
    obtain ⟨g,hg⟩ := ih
    simpa [Nat.pow_succ] using cyclic_product_fin (Nat.pow_pos hm) hm g f hg hf

/-- A single interval coloring on an odd base produces interval colorings
at every length bounded by a power of that base. -/
theorem interval_power_bound {m k N : Nat} (odd : m%2=1) (f : Nat → Fin k)
    (hf : IntervalValid m f) (t : Nat) (size : N≤m^t) :
    ∃ g : Nat → Fin ((12*k)^t), IntervalValid N g := by
  obtain ⟨u,hu⟩ := interval_to_odd_cyclic odd f hf
  obtain ⟨g,hg⟩ := cyclic_power (show 0<m by omega) u hu t
  exact ⟨g, restrict_cyclic hg size⟩

end Erdos160.CyclicTransfer

#print axioms Erdos160.CyclicTransfer.cyclic_power
#print axioms Erdos160.CyclicTransfer.restrict_cyclic
