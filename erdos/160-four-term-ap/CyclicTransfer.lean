module

public import Lean

/-! A 12-tag transfer from integer intervals to odd cyclic groups.
Positions and representatives are indexed from zero. -/
@[expose] public section

namespace Erdos160.CyclicTransfer

def Three (a b c d : α) : Prop :=
  (a ≠ b ∧ a ≠ c ∧ b ≠ c) ∨ (a ≠ b ∧ a ≠ d ∧ b ≠ d) ∨
  (a ≠ c ∧ a ≠ d ∧ c ≠ d) ∨ (b ≠ c ∧ b ≠ d ∧ c ≠ d)

private def Few (a b c d : α) : Prop :=
  (a=b ∧ b=c) ∨ (b=c ∧ c=d) ∨ (a=b ∧ b=d) ∨ (a=c ∧ c=d) ∨
  (a=c ∧ b=d) ∨ (a=d ∧ b=c) ∨ (a=b ∧ c=d)

private theorem few_iff {a b c d : α} : Few a b c d ↔ ¬ Three a b c d := by
  unfold Few Three
  grind

private theorem three_reverse {a b c d : α} : Three d c b a ↔ Three a b c d := by
  unfold Three
  grind

/-- The three fields take respectively two, two, and three values. -/
structure Tag where
  parity : Fin 2
  lower : Bool
  band : Fin 3
  deriving DecidableEq

def lower (m x : Nat) : Bool := decide (2*x < m)
def distance (m x : Nat) : Nat := if 2*x < m then 2*x+1 else 2*(m-x)-1

def tag (m x : Nat) : Tag :=
  ⟨Fin.ofNat 2 x, lower m x, Fin.ofNat 3 (distance m x).log2⟩

def refined (m : Nat) (color : Nat → α) (x : Nat) : α × Tag := (color x, tag m x)

def IntervalValid (m : Nat) (color : Nat → α) : Prop :=
  ∀ a s : Nat, 0 < s → a+3*s < m →
    Three (color a) (color (a+s)) (color (a+2*s)) (color (a+3*s))

private theorem log2_mono {x y : Nat} (hx : x ≠ 0) (h : x ≤ y) : x.log2 ≤ y.log2 :=
  (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le hx) h)

/-- If a positive distance grows by a factor between two and three, its
dyadic exponent changes by one or two and therefore changes modulo three. -/
theorem band_separates {x y : Nat} (hx : 0 < x) (low : 2*x ≤ y) (high : y ≤ 3*x) :
    x.log2 % 3 ≠ y.log2 % 3 := by
  have h1 := log2_mono (x:=2*x) (by omega) low
  have h2 := log2_mono (x:=y) (y:=2*(2*x)) (by omega) (by omega)
  rw [Nat.log2_two_mul (by omega)] at h1
  rw [Nat.log2_two_mul (by omega), Nat.log2_two_mul (by omega)] at h2
  omega

abbrev Next (m s x y : Nat) := x+s = y ∨ x+s = m+y

private theorem parity_eq {m x y : Nat} {f : Nat → α} (h : refined m f x = refined m f y) :
    x % 2 = y % 2 := congrArg (fun z => z.2.parity.val) h

private theorem lower_eq {m x y : Nat} {f : Nat → α} (h : refined m f x = refined m f y) :
    lower m x = lower m y := congrArg (fun z => z.2.lower) h

private theorem band_eq {m x y : Nat} {f : Nat → α} (h : refined m f x = refined m f y) :
    (distance m x).log2 % 3 = (distance m y).log2 % 3 := congrArg (fun z => z.2.band.val) h

private theorem same_half {m s x y : Nat} (hs : 2*s ≤ m) (hx : x < m)
    (step : Next m s x y) (eq : lower m x = lower m y) : x+s = y := by
  rcases step with h | h
  · exact h
  · have a : ¬2*x<m := by omega
    have b : 2*y<m := by omega
    simp [lower,a,b] at eq

private theorem parity_two {m s x y z : Nat} (odd : m % 2 = 1) (hs : 2*s ≤ m)
    (hx : x < m) (hxy : Next m s x y) (hyz : Next m s y z)
    (p : x % 2 = z % 2) : x+s=y ∧ y+s=z := by
  rcases hxy with h|h <;> rcases hyz with k|k <;> omega

/-- A block boundary in the middle of AABB would separate one of the
equal-tag pairs by its dyadic band. -/
theorem aabb_lifts {m s a b c d : Nat} {f : Nat → α} (hs : 2*s ≤ m)
    (ha : a<m) (hb : b<m) (hc : c<m) (_hd : d<m)
    (ab : Next m s a b) (bc : Next m s b c) (cd : Next m s c d)
    (p : refined m f a = refined m f b) (q : refined m f c = refined m f d) :
    a+s=b ∧ b+s=c ∧ c+s=d := by
  have e1 := same_half hs ha ab (lower_eq p)
  have e3 := same_half hs hc cd (lower_eq q)
  refine ⟨e1, ?_, e3⟩
  rcases bc with e2|wrap
  · exact e2
  · exfalso
    have bh : ¬2*b<m := by omega
    have cl : 2*c<m := by omega
    have ah : ¬2*a<m := by
      intro ax
      have := lower_eq p
      simp [lower,bh,show 2*a<m by omega] at this
    have dl : 2*d<m := by
      by_cases dx : 2*d < m
      · exact dx
      · have := lower_eq q
        simp [lower,cl,dx] at this
    have outer := band_eq p
    have inner := band_eq q
    simp [distance,ah,bh] at outer
    simp [distance,cl,dl] at inner
    by_cases bigger : 2*c+1 ≤ 2*(m-b)-1
    · apply (band_separates (x:=2*(m-b)-1) (y:=2*(m-a)-1) (by omega) (by omega) (by omega))
      exact outer.symm
    · apply (band_separates (x:=2*c+1) (y:=2*d+1) (by omega) (by omega) (by omega))
      exact inner

private theorem three_lifts (π : β → α) {a b c d : β}
    (h : Three (π a) (π b) (π c) (π d)) : Three a b c d := by
  unfold Three at *
  grind

private theorem no_mono_triple {m s a b c : Nat} {f : Nat → α} (hf : IntervalValid m f)
    (hs : 0<s) (small : 2*s≤m) (ha : a<m) (hb : b<m) (hc : c<m)
    (ab : Next m s a b) (bc : Next m s b c)
    (p : refined m f a = refined m f b) (q : refined m f b = refined m f c) : False := by
  have u := same_half small ha ab (lower_eq p)
  have v := same_half small hb bc (lower_eq q)
  have ca : f a = f b := congrArg Prod.fst p
  have cb : f b = f c := congrArg Prod.fst q
  by_cases lc : 2*c < m
  · have ok := hf a s hs (by omega)
    simp [Three, u, show a+2*s = c by omega, ca, cb] at ok
  · have la : ¬2*a < m := by
      intro h
      have z := lower_eq (p.trans q)
      simp [lower,h,lc] at z
    have ok := hf (a-s) s hs (by omega)
    simp [Three, show a-s+s = a by omega, show a-s+2*s=b by omega,
      show a-s+3*s=c by omega, ca, cb] at ok

private theorem small_step {m s a b c d : Nat} {f : Nat → α} (odd : m%2=1)
    (hf : IntervalValid m f) (hs : 0<s) (small : 2*s≤m)
    (ha : a<m) (hb : b<m) (hc : c<m) (hd : d<m)
    (ab : Next m s a b) (bc : Next m s b c) (cd : Next m s c d) :
    Three (refined m f a) (refined m f b) (refined m f c) (refined m f d) := by
  have ordinary (u : a+s=b) (v : b+s=c) (w : c+s=d) :
      Three (refined m f a) (refined m f b) (refined m f c) (refined m f d) := by
    apply three_lifts Prod.fst
    change Three (f a) (f b) (f c) (f d)
    simpa only [u, show a+2*s=c by omega, show a+3*s=d by omega] using hf a s hs (by omega)
  apply Classical.byContradiction
  intro fail
  rcases few_iff.mpr fail with ⟨p,q⟩ | ⟨p,q⟩ | ⟨p,q⟩ | ⟨p,q⟩ | ⟨p,q⟩ | ⟨p,q⟩ | ⟨p,q⟩
  · exact no_mono_triple hf hs small ha hb hc ab bc p q
  · exact no_mono_triple hf hs small hb hc hd bc cd p q
  · obtain ⟨v,w⟩ := parity_two odd small hb bc cd (parity_eq q)
    exact fail (ordinary (same_half small ha ab (lower_eq p)) v w)
  · obtain ⟨u,v⟩ := parity_two odd small ha ab bc (parity_eq p)
    exact fail (ordinary u v (same_half small hc cd (lower_eq q)))
  · obtain ⟨u,v⟩ := parity_two odd small ha ab bc (parity_eq p)
    obtain ⟨_,w⟩ := parity_two odd small hb bc cd (parity_eq q)
    exact fail (ordinary u v w)
  · have v := same_half small hb bc (lower_eq q)
    have adp := parity_eq p
    have bcp := parity_eq q
    rcases ab with u|u <;> rcases cd with w|w
    · exact fail (ordinary u v w)
    · omega
    · omega
    · have lo : 2*b<m := by omega
      have hi : ¬2*c<m := by omega
      have z := lower_eq q
      simp [lower,lo,hi] at z
  · obtain ⟨u,v,w⟩ := aabb_lifts small ha hb hc hd ab bc cd p q
    exact fail (ordinary u v w)

private theorem reverse_step {m s x y : Nat} (hs : s<m) (h : Next m s x y) :
    Next m (m-s) y x := by
  rcases h with e|e
  · right; omega
  · left; omega

private theorem next_mod {m s x : Nat} (hx : x<m) (hs : s<m) : Next m s x ((x+s)%m) := by
  by_cases small : x+s<m
  · left; exact (Nat.mod_eq_of_lt small).symm
  · right
    rw [Nat.mod_eq_sub_mod (by omega : m≤x+s), Nat.mod_eq_of_lt (by omega)]
    omega

/-- A nonzero step in the cyclic group uses representatives in [0,m). -/
def CyclicValid (m : Nat) (g : Nat → α) : Prop :=
  ∀ a s : Nat, a<m → 0<s → s<m →
    let b := (a+s)%m
    let c := (b+s)%m
    let d := (c+s)%m
    Three (g a) (g b) (g c) (g d)

/-- The product palette incurs exactly 2 × 2 × 3 additional labels. -/
theorem refined_valid {m : Nat} {f : Nat → α} (odd : m%2=1) (hf : IntervalValid m f) :
    CyclicValid m (refined m f) := by
  intro a s ha hs hm
  let b := (a+s)%m
  let c := (b+s)%m
  let d := (c+s)%m
  change Three (refined m f a) (refined m f b) (refined m f c) (refined m f d)
  have hb : b<m := Nat.mod_lt _ (by omega)
  have hc : c<m := Nat.mod_lt _ (by omega)
  have hd : d<m := Nat.mod_lt _ (by omega)
  have ab : Next m s a b := next_mod ha hm
  have bc : Next m s b c := next_mod hb hm
  have cd : Next m s c d := next_mod hc hm
  by_cases small : 2*s≤m
  · exact small_step odd hf hs small ha hb hc hd ab bc cd
  · apply three_reverse.mp
    exact small_step odd hf (by omega : 0<m-s) (by omega) hd hc hb ha
      (reverse_step hm cd) (reverse_step hm bc) (reverse_step hm ab)

private def encode {k : Nat} (z : Fin k × Tag) : Fin (12*k) :=
  ⟨12*z.1.val + 6*z.2.parity.val + 3*(if z.2.lower then 1 else 0) + z.2.band.val, by
    have := z.1.isLt
    have := z.2.parity.isLt
    have := z.2.band.isLt
    cases z.2.lower <;> simp <;> omega⟩

private theorem encode_injective {k : Nat} {x y : Fin k × Tag} (h : encode x = encode y) : x=y := by
  rcases x with ⟨i,⟨p,b,t⟩⟩
  rcases y with ⟨j,⟨q,c,u⟩⟩
  have v := congrArg Fin.val h
  have hp := p.isLt
  have hq := q.isLt
  have ht := t.isLt
  have hu := u.isLt
  cases b <;> cases c <;> simp [encode] at v <;>
    first | omega | exact (by
      have ij : i=j := Fin.ext (by omega)
      have pq : p=q := Fin.ext (by omega)
      have tu : t=u := Fin.ext (by omega)
      simp [ij,pq,tu])

/-- Every valid k-coloring of [0,m) produces a valid 12k-coloring of the cyclic
group of residues modulo m, for every odd natural number m. -/
theorem interval_to_odd_cyclic {m k : Nat} (odd : m%2=1) (f : Nat → Fin k) (hf : IntervalValid m f) :
    ∃ g : Nat → Fin (12*k), CyclicValid m g := by
  refine ⟨fun x => encode (refined m f x), ?_⟩
  intro a s ha hs hm
  have good := refined_valid odd hf a s ha hs hm
  dsimp at good ⊢
  unfold Three at good ⊢
  grind [encode_injective]

end Erdos160.CyclicTransfer

#print axioms Erdos160.CyclicTransfer.interval_to_odd_cyclic
