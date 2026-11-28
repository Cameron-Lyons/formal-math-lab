import ExactParity

/-! Natural F₃ power moments for the original board predicate. All finite
arithmetic checks use kernel reduction (`decide`), not native evaluation. -/
namespace TBoards.ExactNativeMoments

abbrev F3 := Fin 3
abbrev Table := F3 → F3 → F3 → F3 → F3

def at3 (x y z : F3) (i : F3) : F3 :=
  if i = 0 then x else if i = 1 then y else z

theorem at3_apply (f : F3 → F3) (i : F3) : at3 (f 0) (f 1) (f 2) i = f i := by
  rcases i with ⟨i,hi⟩
  have he : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl | rfl <;> simp [at3]

def tr (x y z e : F3) : F3 :=
  (0 : F3)^e.val * x + (1 : F3)^e.val * y + (2 : F3)^e.val * z

def iv (x y z c : F3) : F3 := at3 (x + 2*z) (2*y + 2*z) (y + 2*z) c

private theorem inverse_values : ∀ x y z c : F3,
    iv (tr x y z 0) (tr x y z 1) (tr x y z 2) c = at3 x y z c := by decide

def transform (f : F3 → F3) (e : F3) : F3 := tr (f 0) (f 1) (f 2) e
def inverse (f : F3 → F3) (c : F3) : F3 := iv (f 0) (f 1) (f 2) c

theorem inverse_transform (f : F3 → F3) (c : F3) : inverse (transform f) c = f c := by
  exact (inverse_values (f 0) (f 1) (f 2) c).trans (at3_apply f c)

def moment (f : Table) (i j k l : F3) : F3 :=
  transform (fun a => transform (fun b => transform
    (fun c => transform (fun d => f a b c d) l) k) j) i

def recover (f : Table) (a b c d : F3) : F3 :=
  inverse (fun l => inverse (fun k => inverse
    (fun j => inverse (fun i => f i j k l) a) b) c) d

theorem recover_moment (f : Table) (a b c d : F3) :
    recover (moment f) a b c d = f a b c d := by
  simp only [recover, moment, inverse_transform]

def target (i j k l : F3) : F3 :=
  if i = 2 ∧ j = 2 ∧ k = 2 ∧ l = 2 then 1 else 0

theorem moment_one : ∀ i j k l : F3,
    moment (fun _ _ _ _ => 1) i j k l = target i j k l := by decide

theorem moments_iff_one (f : Table) :
    (∀ i j k l, moment f i j k l = target i j k l) ↔
      ∀ a b c d, f a b c d = 1 := by
  constructor
  · intro h a b c d
    have ht : moment f = moment (fun _ _ _ _ => 1) := by
      funext i j k l
      exact (h i j k l).trans (moment_one i j k l).symm
    have hr := congrArg (fun g => recover g a b c d) ht
    simpa only [recover_moment] using hr
  · intro h i j k l
    have hf : f = (fun _ _ _ _ => 1) := by funext a b c d; exact h a b c d
    rw [hf]
    exact moment_one i j k l

def residue (n : Nat) : F3 := Fin.ofNat 3 n
def counts (ps : List Pattern) : Table := fun a b c d =>
  residue (ps.count (a.val,b.val,c.val,d.val))

private theorem residue_add (m n : Nat) : residue (m+n) = residue m + residue n := by
  apply Fin.ext
  simp [residue, Fin.val_add, Nat.add_mod]

private theorem tr_add : ∀ a b c x y z e : F3,
    tr (a+x) (b+y) (c+z) e = tr a b c e + tr x y z e := by decide

theorem transform_add (f g : F3 → F3) (e : F3) :
    transform (fun x => f x + g x) e = transform f e + transform g e :=
  tr_add (f 0) (f 1) (f 2) (g 0) (g 1) (g 2) e

theorem moment_add (f g : Table) (i j k l : F3) :
    moment (fun a b c d => f a b c d + g a b c d) i j k l =
      moment f i j k l + moment g i j k l := by
  simp only [moment, transform_add]

def spike (p : Pattern) : Table := fun a b c d =>
  if p = (a.val,b.val,c.val,d.val) then 1 else 0

theorem counts_cons (p : Pattern) (ps : List Pattern) :
    counts (p::ps) = fun a b c d => counts ps a b c d + spike p a b c d := by
  funext a b c d
  simp only [counts, List.count_cons, residue_add]
  by_cases h : p = (a.val,b.val,c.val,d.val) <;> simp [spike, h, residue]

private theorem spike_constant_values : ∀ a b c d : F3,
    moment (spike (a.val,b.val,c.val,d.val)) 0 0 0 0 = 1 := by decide

theorem spike_constant (p : Pattern) (hp : ColorPattern p) :
    moment (spike p) 0 0 0 0 = 1 := by
  rcases p with ⟨a,b,c,d⟩
  exact spike_constant_values ⟨a,hp.1⟩ ⟨b,hp.2.1⟩ ⟨c,hp.2.2.1⟩ ⟨d,hp.2.2.2⟩

theorem constant_counts (ps : List Pattern) (hp : ∀ p ∈ ps, ColorPattern p) :
    moment (counts ps) 0 0 0 0 = residue ps.length := by
  induction ps with
  | nil => decide
  | cons p ps ih =>
    rw [counts_cons, moment_add, spike_constant p (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))]
    rw [List.length_cons, residue_add]
    rfl

theorem constant_board_moment (b : Board) (hw : WellFormed b) :
    moment (counts (patterns b)) 0 0 0 0 = 0 := by
  rw [constant_counts _ (fun _ hp => hw.pattern_colors hp), patterns_length]
  rfl

def AllMoments (b : Board) : Prop :=
  ∀ i j k l, moment (counts (patterns b)) i j k l = target i j k l

theorem valid_iff_all_moments (b : Board) :
    Valid b ↔ WellFormed b ∧ AllMoments b := by
  rw [ExactParity.valid_iff_congruent_one b 3 (by decide)]
  constructor
  · rintro ⟨hw,hc⟩
    refine ⟨hw, (moments_iff_one _).mpr ?_⟩
    intro a l m r
    apply Fin.ext
    exact hc a l m r
  · rintro ⟨hw,hm⟩
    refine ⟨hw, ?_⟩
    intro a l m r
    have h := (moments_iff_one _).mp hm a l m r
    exact congrArg Fin.val h

/-- Precisely the 80 nonconstant power moments. The single nonzero target is
the exponent vector (2,2,2,2), with value one in F₃. -/
def NativeMoments (b : Board) : Prop :=
  ∀ i j k l : F3, ¬(i=0 ∧ j=0 ∧ k=0 ∧ l=0) →
    moment (counts (patterns b)) i j k l = target i j k l

theorem valid_iff_native_moments (b : Board) :
    Valid b ↔ WellFormed b ∧ NativeMoments b := by
  rw [valid_iff_all_moments]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨hw, fun i j k l _ => hm i j k l⟩
  · rintro ⟨hw,hm⟩
    refine ⟨hw, ?_⟩
    intro i j k l
    by_cases hz : i=0 ∧ j=0 ∧ k=0 ∧ l=0
    · rcases hz with ⟨rfl,rfl,rfl,rfl⟩
      exact constant_board_moment b hw
    · exact hm i j k l hz

private theorem tr_mul_left : ∀ a b c s e : F3,
    tr (s*a) (s*b) (s*c) e = s * tr a b c e := by decide

private theorem tr_mul_right : ∀ a b c s e : F3,
    tr (a*s) (b*s) (c*s) e = tr a b c e * s := by decide

theorem transform_mul_left (f : F3 → F3) (s e : F3) :
    transform (fun x => s * f x) e = s * transform f e :=
  tr_mul_left (f 0) (f 1) (f 2) s e

theorem transform_mul_right (f : F3 → F3) (s e : F3) :
    transform (fun x => f x * s) e = transform f e * s :=
  tr_mul_right (f 0) (f 1) (f 2) s e

def indicator (a x : F3) : F3 := if x = a then 1 else 0

private theorem transform_indicator : ∀ a e : F3,
    transform (indicator a) e = a^e.val := by decide

private theorem spike_product : ∀ a b c d x y z w : F3,
    spike (a.val,b.val,c.val,d.val) x y z w =
      indicator a x * indicator b y * indicator c z * indicator d w := by decide

theorem moment_product (f g h v : F3 → F3) (i j k l : F3) :
    moment (fun a b c d => f a*g b*h c*v d) i j k l =
      transform f i * transform g j * transform h k * transform v l := by
  simp only [moment, transform_mul_left, transform_mul_right]

theorem spike_moment_values (a b c d i j k l : F3) :
    moment (spike (a.val,b.val,c.val,d.val)) i j k l =
      a^i.val * b^j.val * c^k.val * d^l.val := by
  have hs : spike (a.val,b.val,c.val,d.val) =
      (fun x y z w => indicator a x * indicator b y * indicator c z * indicator d w) := by
    funext x y z w
    exact spike_product a b c d x y z w
  rw [hs, moment_product]
  simp only [transform_indicator]

def weight (p : Pattern) (i j k l : F3) : F3 :=
  (residue p.1)^i.val * (residue p.2.1)^j.val *
    (residue p.2.2.1)^k.val * (residue p.2.2.2)^l.val

private theorem residue_val (a : F3) : residue a.val = a := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt a.isLt

theorem spike_moment (p : Pattern) (hp : ColorPattern p) (i j k l : F3) :
    moment (spike p) i j k l = weight p i j k l := by
  rcases p with ⟨a,b,c,d⟩
  let aa : F3 := ⟨a,hp.1⟩
  let bb : F3 := ⟨b,hp.2.1⟩
  let cc : F3 := ⟨c,hp.2.2.1⟩
  let dd : F3 := ⟨d,hp.2.2.2⟩
  have hh := spike_moment_values aa bb cc dd i j k l
  change moment (spike (aa.val,bb.val,cc.val,dd.val)) i j k l =
    (residue aa.val)^i.val * (residue bb.val)^j.val *
      (residue cc.val)^k.val * (residue dd.val)^l.val
  simpa only [residue_val] using hh

/-- Direct modular sum of the powers of the four colors at each placement. -/
def powerSum : List Pattern → F3 → F3 → F3 → F3 → F3
  | [], _, _, _, _ => 0
  | p::ps, i, j, k, l => powerSum ps i j k l + weight p i j k l

theorem moment_eq_powerSum (ps : List Pattern)
    (hp : ∀ p ∈ ps, ColorPattern p) (i j k l : F3) :
    moment (counts ps) i j k l = powerSum ps i j k l := by
  induction ps with
  | nil => simp [counts, moment, transform, tr, residue, Fin.mul_zero, powerSum]
  | cons p ps ih =>
    rw [counts_cons, moment_add, spike_moment p (hp p (by simp)),
      ih (fun q hq => hp q (by simp [hq]))]
    rfl

def PowerMoments (b : Board) : Prop :=
  ∀ i j k l : F3, ¬(i=0 ∧ j=0 ∧ k=0 ∧ l=0) →
    powerSum (patterns b) i j k l = target i j k l

/-- The original board validity predicate is equivalent to precisely the
80 native-F₃ power moments on its actual geometric T placements. -/
theorem valid_iff_power_moments (b : Board) :
    Valid b ↔ WellFormed b ∧ PowerMoments b := by
  rw [valid_iff_native_moments]
  constructor
  · rintro ⟨hw,hm⟩
    refine ⟨hw, ?_⟩
    intro i j k l hn
    rw [← moment_eq_powerSum _ (fun _ hp => hw.pattern_colors hp)]
    exact hm i j k l hn
  · rintro ⟨hw,hm⟩
    refine ⟨hw, ?_⟩
    intro i j k l hn
    rw [moment_eq_powerSum _ (fun _ hp => hw.pattern_colors hp)]
    exact hm i j k l hn

end TBoards.ExactNativeMoments

#print axioms TBoards.ExactNativeMoments.valid_iff_all_moments
#print axioms TBoards.ExactNativeMoments.valid_iff_native_moments
#print axioms TBoards.ExactNativeMoments.valid_iff_power_moments
