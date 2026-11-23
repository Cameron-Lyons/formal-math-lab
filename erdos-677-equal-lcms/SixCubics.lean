import FixedLength
import Height
import Period
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.LinearCombination

namespace Erdos677
open Finset

/-- Triangular coordinate for the six entries starting at `n+1`. -/
def sixCoordinate (n : ℕ) : ℕ := (n + 4).choose 2

/-- The cubic after pairing the six factors symmetric about the block center. -/
def sixCubic (a : ℤ) : ℤ := a * (a-1) * (a-3)

/-- The repeated powers of 4 and 5 in a six-term window give its two
nonconstant factors in the product-to-LCM quotient. -/
def sixCorrection (n : ℕ) : ℕ :=
  (if n % 4 ≥ 2 then 2 else 1) * (if n % 5 = 4 then 5 else 1)

theorem sixCoordinate_square (n : ℕ) : 8 * sixCoordinate n + 1 = (2*n+7)^2 := by
  have h : 2 * sixCoordinate n = (n+4)*(n+3) := by
    unfold sixCoordinate
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd,
      show n+4-1=n+3 by omega]
  nlinarith [h]

theorem sixProduct_eq (n : ℕ) :
    (((n+1).ascFactorial 6 : ℕ) : ℤ) = 8 * sixCubic (sixCoordinate n) := by
  have h := centeredProduct_at_center n 6
  have hs : (2*(n:ℤ)+7)^2 = 8*(sixCoordinate n : ℤ)+1 := by
    exact_mod_cast (sixCoordinate_square n).symm
  rw [centeredProduct_six, Nat.add_descFactorial_eq_ascFactorial] at h
  norm_num only [Nat.cast_ofNat] at h
  rw [show 2*(n:ℤ)+6+1=2*n+7 by ring, hs] at h
  unfold sixCubic
  linarith only [h]

private def lcmDefect (n : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => lcmDefect n k * (lcmInterval n k).gcd (n+k+1)

private theorem lcmDefect_spec (n k : ℕ) :
    lcmDefect n k * lcmInterval n k = (n+1).ascFactorial k := by
  induction k with
  | zero => simp [lcmDefect, lcmInterval]
  | succ k ih =>
    rw [lcmDefect, lcmInterval_extend, mul_assoc, Nat.gcd_mul_lcm, ← mul_assoc, ih,
      Nat.ascFactorial_succ]
    rw [show n+1+k = n+k+1 by omega, mul_comm]

private theorem lcmDefect_period {n d k : ℕ} (hd : ∀ t, 0 < t → t < k → t ∣ d) :
    lcmDefect (n+d) k = lcmDefect n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lcmDefect, lcmDefect, ih (fun t ht ht' => hd t ht (by omega))]
    by_cases hk : k=0
    · subst k; simp [lcmInterval]
    · rw [gcd_next_periodic (n := n) (d := d) (by omega) (fun t ht ht' => hd t ht (by omega))]

theorem six_lcm_formula (n : ℕ) :
    12 * sixCorrection n * lcmInterval n 6 = (n+1).ascFactorial 6 := by
  have hdiv : ∀ t : Fin 6, 0 < t.val → t.val ∣ 60 := by decide
  have htab : ∀ t : Fin 60, lcmDefect t.val 6 = 12 * sixCorrection t.val := by decide
  have hp := lcmDefect_period (n := n%60) (d := 60*(n/60)) (k := 6)
    (fun t ht ht' => (hdiv ⟨t,ht'⟩ ht).trans (dvd_mul_right ..))
  rw [Nat.mod_add_div, htab ⟨n%60, Nat.mod_lt _ (by decide)⟩] at hp
  have hc : sixCorrection (n%60) = sixCorrection n := by
    simp only [sixCorrection, Nat.mod_mod_of_dvd n (by decide : 4 ∣ 60),
      Nat.mod_mod_of_dvd n (by decide : 5 ∣ 60)]
  rw [← hc, ← hp]
  exact lcmDefect_spec ..

private theorem sixCubic_lcm (n : ℕ) :
    3 * (sixCorrection n : ℤ) * (lcmInterval n 6 : ℕ) = 2 * sixCubic (sixCoordinate n) := by
  have h := congrArg (fun x : ℕ => (x:ℤ)) (six_lcm_formula n)
  push_cast at h
  linarith only [h, sixProduct_eq n]

private theorem sixCorrection_pos (n : ℕ) : 0 < sixCorrection n := by
  unfold sixCorrection
  split <;> split <;> decide

/-- The coordinates and their corrections specify a necessary and sufficient
equation for LCM equality, for arbitrary starts. -/
theorem six_collision_iff {m n : ℕ} : lcmInterval m 6 = lcmInterval n 6 ↔
    (sixCorrection n : ℤ) * sixCubic (sixCoordinate m) =
    (sixCorrection m : ℤ) * sixCubic (sixCoordinate n) := by
  have hm := sixCubic_lcm m
  have hn := sixCubic_lcm n
  have hcn : (0:ℤ) < sixCorrection n := by exact_mod_cast sixCorrection_pos n
  have hcm : (0:ℤ) < sixCorrection m := by exact_mod_cast sixCorrection_pos m
  have hident :
      (3*(sixCorrection n : ℤ)*sixCorrection m) *
          ((lcmInterval m 6 : ℕ) - ((lcmInterval n 6 : ℕ) : ℤ)) =
      2 * ((sixCorrection n : ℤ)*sixCubic (sixCoordinate m) -
            (sixCorrection m : ℤ)*sixCubic (sixCoordinate n)) := by
    linear_combination (sixCorrection n : ℤ)*hm - (sixCorrection m : ℤ)*hn
  constructor
  · intro h
    rw [h] at hident
    linarith only [hident]
  · intro h
    rw [h, sub_self, mul_zero] at hident
    have hpos : (3:ℤ)*sixCorrection n*sixCorrection m ≠ 0 := by positivity
    have he := sub_eq_zero.mp ((mul_eq_zero.mp hident).resolve_left hpos)
    exact_mod_cast he

private theorem sixCorrection_values (n : ℕ) :
    sixCorrection n = 1 ∨ sixCorrection n = 2 ∨ sixCorrection n = 5 ∨ sixCorrection n = 10 := by
  unfold sixCorrection
  split <;> split <;> decide

/-- Later starts give larger products. Equal LCMs therefore require a strict
increase in the correction factor, which depends only on the start modulo 20. -/
theorem six_collision_correction_lt {m n : ℕ} (hlt : n < m)
    (heq : lcmInterval m 6 = lcmInterval n 6) : sixCorrection n < sixCorrection m := by
  have hprod : (n+1).ascFactorial 6 < (m+1).ascFactorial 6 := by
    simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero]
    gcongr
  rw [← six_lcm_formula n, ← six_lcm_formula m, heq] at hprod
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_right hprod)

/-- The four affine cubic equations using positive triangular coordinates. -/
def onSixCubics (a b : ℤ) : Prop :=
  sixCubic b = 2*sixCubic a ∨ 2*sixCubic b = 5*sixCubic a ∨
  sixCubic b = 5*sixCubic a ∨ sixCubic b = 10*sixCubic a

theorem six_collision_on_cubics {m n : ℕ} (hlt : n < m)
    (heq : lcmInterval m 6 = lcmInterval n 6) :
    onSixCubics (sixCoordinate n) (sixCoordinate m) := by
  have hlt' := six_collision_correction_lt hlt heq
  have h := six_collision_iff.mp heq
  dsimp only [onSixCubics]
  rcases sixCorrection_values n with H|H|H|H <;>
    rcases sixCorrection_values m with K|K|K|K <;>
    simp only [H,K,Nat.cast_ofNat] at h hlt' <;> omega

/-- Recover a start from an integral cubic coordinate. The check below rejects
coordinates where the square root and division do not give an inverse. -/
def sixStart (a : ℕ) : ℕ := (Nat.sqrt (8*a+1) - 7)/2

theorem sixStart_coordinate (n : ℕ) : sixStart (sixCoordinate n) = n := by
  rw [sixStart, sixCoordinate_square, Nat.sqrt_eq']
  omega

/-- Verify that a nonnegative affine point describes two disjoint length-six
blocks with equal LCM. -/
def sixCandidate (a b : ℕ) : Bool :=
  let n := sixStart a
  let m := sixStart b
  decide (sixCoordinate n = a ∧ sixCoordinate m = b ∧ n+6 ≤ m ∧
    (sixCorrection n : ℤ)*sixCubic b = (sixCorrection m : ℤ)*sixCubic a)

theorem sixCandidate_iff {a b : ℕ} : sixCandidate a b = true ↔
    ∃ n m : ℕ, sixCoordinate n = a ∧ sixCoordinate m = b ∧ n+6 ≤ m ∧
      lcmInterval m 6 = lcmInterval n 6 := by
  simp only [sixCandidate, decide_eq_true_eq]
  constructor
  · rintro ⟨ha,hb,hdis,heq⟩
    refine ⟨_,_,ha,hb,hdis,six_collision_iff.mpr ?_⟩
    rwa [ha,hb]
  · rintro ⟨n,m,rfl,rfl,hdis,heq⟩
    simpa only [sixStart_coordinate, true_and] using
      And.intro (rfl : sixCoordinate n = sixCoordinate n)
      (And.intro (rfl : sixCoordinate m = sixCoordinate m) (And.intro hdis (six_collision_iff.mp heq)))

/-- The point (36,45) lies on the ratio-two curve and corresponds to the
overlapping blocks with starts 5 and 6. -/
theorem six_overlapping_control :
    sixCubic 45 = 2*sixCubic 36 ∧ sixStart 36 = 5 ∧ sixStart 45 = 6 ∧
    lcmInterval (5:ℕ) 6 = 27720 ∧ lcmInterval (6:ℕ) 6 = 27720 ∧ sixCandidate 36 45 = false := by
  norm_num [sixCubic, sixStart, sixCandidate, sixCoordinate, sixCorrection, lcmInterval]
  decide +kernel

/-- Every affine point found by the signed search, with duplicates between
different curves removed. The nine pairs of roots occur on every curve. -/
def observedSixPoints : List (ℕ × ℕ) :=
  [(0,0),(0,1),(0,3),(1,0),(1,1),(1,3),(3,0),(3,1),(3,3),
   (13,16),(36,45),(136,171),(21,28),(17,35)]

theorem observedSixPoints_rejected : observedSixPoints.all
    (fun ab => !sixCandidate ab.1 ab.2) = true := by decide +kernel

theorem observedSixPoints_on_cubics :
    ∀ ab ∈ observedSixPoints, onSixCubics ab.1 ab.2 := by
  simp [observedSixPoints, onSixCubics, sixCubic]

/-- The three genuine LCM equalities among the nonzero points have overlapping
blocks. The remaining two nonzero points lack triangular coordinates. -/
theorem other_six_controls :
    (sixStart 21, sixStart 28) = (3,4) ∧ (sixStart 136, sixStart 171) = (13,15) ∧
    lcmInterval (3:ℕ) 6 = 2520 ∧ lcmInterval (4:ℕ) 6 = 2520 ∧
    lcmInterval (13:ℕ) 6 = 1627920 ∧ lcmInterval (15:ℕ) 6 = 1627920 ∧
    sixCoordinate (sixStart 13) ≠ 13 ∧ sixCoordinate (sixStart 17) ≠ 17 := by
  decide +kernel

/-- A complete cover of the nonnegative points on the four affine cubics by
the displayed list would settle the unbounded length-six case. -/
theorem no_collision_six_of_affine_cover
    (cover : ∀ a b : ℕ, onSixCubics a b → (a,b) ∈ observedSixPoints)
    {n m : ℕ} (hd : n+6 ≤ m) : lcmInterval m 6 ≠ lcmInterval n 6 := by
  intro heq
  have hab := cover _ _ (six_collision_on_cubics (by omega) heq)
  have rejected := List.all_eq_true.mp observedSixPoints_rejected _ hab
  have accepted := sixCandidate_iff.mpr ⟨n,m,rfl,rfl,hd,heq⟩
  simp [accepted] at rejected

/-- Among all distinct six-term blocks, the complete affine-point list
gives exactly three equalities. Each pair overlaps. -/
theorem six_collision_iff_three_of_affine_cover
    (cover : ∀ a b : ℕ, onSixCubics a b → (a,b) ∈ observedSixPoints)
    {n m : ℕ} (hlt : n < m) : lcmInterval m 6 = lcmInterval n 6 ↔
      (n,m) = (3,4) ∨ (n,m) = (5,6) ∨ (n,m) = (13,15) := by
  let triangular (ab : ℕ × ℕ) : Bool := decide (
    sixCoordinate (sixStart ab.1) = ab.1 ∧ sixCoordinate (sixStart ab.2) = ab.2)
  let starts (ab : ℕ × ℕ) := (sixStart ab.1, sixStart ab.2)
  have table : (observedSixPoints.filter triangular).map starts = [(5,6),(13,15),(3,4)] := by
    decide +kernel
  constructor
  · intro heq
    have hab := cover _ _ (six_collision_on_cubics hlt heq)
    have htri : (sixCoordinate n, sixCoordinate m) ∈ observedSixPoints.filter triangular :=
      List.mem_filter.mpr ⟨hab, by simp [triangular, sixStart_coordinate]⟩
    have hl := List.mem_map_of_mem (f := starts) htri
    rw [table] at hl
    simp only [starts, sixStart_coordinate, List.mem_cons] at hl
    tauto
  · rintro (h|h|h) <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> decide +kernel

/-- The analytic height bound for the four plane cubics suffices to remove
the height limit in the kernel-checked exclusion for length six. -/
theorem no_collision_six_of_affine_bound
    (bound : ∀ a b : ℕ, 4 ≤ a → a < b → onSixCubics a b → a ≤ 13000 * 10^16)
    {n m : ℕ} (hd : n+6 ≤ m) : lcmInterval m 6 ≠ lcmInterval n 6 := by
  intro heq
  have hA := sixCoordinate_square n
  have hB := sixCoordinate_square m
  have hmin : 4 ≤ sixCoordinate n := by nlinarith
  have hg : (2*n+7)^2 < (2*m+7)^2 := by
    gcongr
    omega
  have hlt : sixCoordinate n < sixCoordinate m := by omega
  have hb := bound _ _ hmin hlt (six_collision_on_cubics (by omega) heq)
  apply no_collision_five_six (Or.inr rfl) hd _ heq
  by_contra! hn
  have huge : (2*10^20+7)^2 < (2*n+7)^2 := by gcongr
  norm_num at huge hb
  omega

end Erdos677
