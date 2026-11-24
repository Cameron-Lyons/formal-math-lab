module

public import PoleOneDegree
import PellConstantFiber
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section
namespace SmallCubic
open Polynomial

private noncomputable abbrev embed := algebraMap ℚ[X] (RatFunc ℚ)

/-- Rational functions regular away from the two roots of an irreducible quadratic
L, including at t = ∞. For the rational parametrization of the Pell torus, L = 1 − Dt². -/
def PellRegular (L : ℚ[X]) (f : RatFunc ℚ) : Prop :=
  ∃ (m : ℕ) (A : ℚ[X]), A.natDegree ≤ 2 * m ∧ f * algebraMap ℚ[X] (RatFunc ℚ) L ^ m = algebraMap ℚ[X] (RatFunc ℚ) A

/-- Cancel factors of the quadratic denominator to obtain the exact pole order. -/
theorem PellRegular.exists_reduced {L : ℚ[X]} {f : RatFunc ℚ}
    (hL : L.natDegree = 2) (hf : f ≠ 0) (h : PellRegular L f) :
    ∃ (m : ℕ) (A : ℚ[X]), A.natDegree ≤ 2*m ∧ ¬ L ∣ A ∧
      f * algebraMap ℚ[X] (RatFunc ℚ) L ^ m = algebraMap ℚ[X] (RatFunc ℚ) A := by
  have lne : L ≠ 0 := fun H => by simp [H] at hL
  have en := RatFunc.algebraMap_ne_zero lne
  obtain ⟨m, A, d, eq⟩ := h
  induction m generalizing A with
  | zero =>
    refine ⟨0, A, d, ?_, eq⟩
    intro hd
    have ha : A ≠ 0 := by rintro rfl; simp at eq; contradiction
    have := natDegree_le_of_dvd hd ha
    omega
  | succ m ih =>
    by_cases hd : L ∣ A
    · obtain ⟨Q, rfl⟩ := hd
      have qne : Q ≠ 0 := by
        rintro rfl
        simp [en, hf] at eq
      rw [natDegree_mul lne qne, hL] at d
      apply ih Q (by omega)
      apply mul_right_cancel₀ en
      simpa [pow_succ, ← mul_assoc, map_mul, mul_comm (embed L) (embed Q)] using eq
    · exact ⟨m+1,A,d,hd,eq⟩

/-- The second factor of 2 − x³ is regular whenever y and z are. -/
theorem PellRegular.add_sq {L : ℚ[X]} (hL : L.natDegree = 2)
    {z y : RatFunc ℚ} (hz : PellRegular L z) (hy : PellRegular L y) :
    PellRegular L (z + y^2) := by
  obtain ⟨a,A,da,ea⟩ := hz
  obtain ⟨b,B,db,eb⟩ := hy
  refine ⟨a+2*b,A*L^(2*b)+B^2*L^a, ?_, ?_⟩
  · apply (natDegree_add_le _ _).trans
    apply max_le <;> apply natDegree_mul_le.trans
    · rw [natDegree_pow, hL]; omega
    · rw [natDegree_pow, natDegree_pow, hL]; omega
  · rw [map_add, map_mul, map_mul, map_pow, map_pow, map_pow, ← ea, ← eb, pow_add, pow_mul]
    ring

/-- Two fractions with numerators coprime to L have unique denominator exponent. -/
private theorem pole_orders_eq {L A B : ℚ[X]} (hp : Prime L) (ha : ¬L ∣ A) (hb : ¬L ∣ B)
    {m n : ℕ} (h : A * L^m = B * L^n) : m = n := by
  have e := congrArg (emultiplicity L) h
  rw [emultiplicity_mul hp, emultiplicity_mul hp, emultiplicity_eq_zero.mpr ha,
    emultiplicity_eq_zero.mpr hb, emultiplicity_pow_self_of_prime hp,
    emultiplicity_pow_self_of_prime hp, zero_add, zero_add] at e
  exact ENat.natCast_inj.mp e

private theorem cross_multiply {L A B : ℚ[X]} {m n : ℕ} {f : RatFunc ℚ}
    (hA : f * embed L ^ m = embed A) (hB : f * embed L ^ n = embed B) :
    A * L ^ n = B * L ^ m := by
  apply RatFunc.algebraMap_injective ℚ
  change embed _ = embed _
  rw [map_mul, map_mul, map_pow, map_pow, ← hA, ← hB]
  ring

/-- A square of a regular function cannot have a reduced denominator L³. -/
private theorem odd_pole_not_square {L Y : ℚ[X]} {y : RatFunc ℚ}
    (hp : Prime L) (dl : L.natDegree = 2) (hY : ¬L ∣ Y)
    (r : PellRegular L y) (eq : y^2 * embed L ^ 3 = embed Y) : False := by
  have yn : y ≠ 0 := by
    rintro rfl
    have := RatFunc.algebraMap_injective ℚ
    have hy0 : Y = 0 := this (by simpa [embed] using eq.symm)
    exact hY (hy0 ▸ dvd_zero L)
  obtain ⟨n,B,_,hB,eB⟩ := PellRegular.exists_reduced dl yn r
  have eq' : y^2 * embed L ^ (n*2) = embed (B^2) := by
    rw [map_pow, ← eB, pow_mul, mul_pow]
  have hn := pole_orders_eq hp hY (fun h => hB (hp.dvd_of_dvd_pow h)) (cross_multiply eq eq')
  omega

/-- In reduced fractions x = X/Lᵏ, z = A/Lᵐ, w = B/Lⁿ, the factorization
zw = 2 − x³ forces 3 ∣ m, 3 ∣ n, and m + n = 3k. The degree bounds express
regularity at t = ∞. This holds for every positive pole order k of x. -/
theorem pell_factor_pole_orders {L X A B : ℚ[X]} {k m n : ℕ}
    (hp : Irreducible L) (dL : L.natDegree = 2) (hk : 0 < k)
    (dX : X.natDegree ≤ 2*k) (dA : A.natDegree ≤ 2*m) (dB : B.natDegree ≤ 2*n)
    (hX : ¬ L ∣ X) (hA : ¬ L ∣ A) (hB : ¬ L ∣ B)
    {x z w : RatFunc ℚ} (hzw : z*w = 2 - x^3)
    (hx : x * algebraMap ℚ[X] (RatFunc ℚ) L ^ k = algebraMap ℚ[X] (RatFunc ℚ) X)
    (hz : z * algebraMap ℚ[X] (RatFunc ℚ) L ^ m = algebraMap ℚ[X] (RatFunc ℚ) A)
    (hw : w * algebraMap ℚ[X] (RatFunc ℚ) L ^ n = algebraMap ℚ[X] (RatFunc ℚ) B) :
    m + n = 3*k ∧ 3 ∣ m ∧ 3 ∣ n := by
  let F := 2 * (L^k)^3 - X^3
  have cop : ¬ L ∣ F := by
    intro H
    have hd : L ∣ 2 * (L^k)^3 := dvd_mul_of_dvd_right
      ((dvd_pow_self L hk.ne').trans (dvd_pow_self _ (by decide : 3 ≠ 0))) _
    exact hX (hp.prime.dvd_of_dvd_pow ((dvd_sub_right hd).mp H))
  have degLk : (L^k).natDegree = 2*k := by rw [natDegree_pow,dL]; omega
  have dF := cube_difference_degree_of_le (pow_ne_zero k hp.ne_zero) (dX.trans degLk.ge)
  change F.natDegree = _ at dF
  rw [degLk] at dF
  change x * embed L ^ k = embed X at hx
  change z * embed L ^ m = embed A at hz
  change w * embed L ^ n = embed B at hw
  have eF : (z*w) * embed L ^ (3*k) = embed F := by
    rw [hzw]
    simp only [F, map_sub, map_mul, map_pow, map_ofNat, ← hx]
    rw [Nat.mul_comm, pow_mul]; ring
  have eAB : (z*w) * embed L ^ (m+n) = embed (A*B) := by
    rw [map_mul, ← hz, ← hw, pow_add]; ring
  have ord := pole_orders_eq hp.prime cop (fun h => (hp.prime.dvd_mul.mp h).elim hA hB)
    (cross_multiply eF eAB)
  have eqF : F = A*B := by
    apply RatFunc.algebraMap_injective ℚ
    change embed F = embed (A*B)
    rw [← eF, ← eAB, ord]
  have an : A ≠ 0 := fun H => hA (H ▸ dvd_zero L)
  have bn : B ≠ 0 := fun H => hB (H ▸ dvd_zero L)
  rw [eqF, natDegree_mul an bn] at dF
  have ma : 3 ∣ A.natDegree := three_dvd_degree_of_cube_factor
    ((hp.coprime_iff_not_dvd.mpr hA).pow_left) (eqF ▸ dvd_mul_right A B)
  have nb : 3 ∣ B.natDegree := three_dvd_degree_of_cube_factor
    ((hp.coprime_iff_not_dvd.mpr hB).pow_left) (eqF ▸ dvd_mul_left B A)
  exact ⟨ord, by omega, by omega⟩

/-- The first coordinate of a solution in regular functions on a nonsplit Pell torus
can never have pole order one. No restrictions are imposed on the orders of y and z. -/
theorem no_pell_pole_one_x {L X : ℚ[X]} (hL : Irreducible L) (dL : L.natDegree = 2)
    (dX : X.natDegree ≤ 2) (hX : ¬ L ∣ X) {x y z : RatFunc ℚ}
    (hx : x * algebraMap ℚ[X] (RatFunc ℚ) L = algebraMap ℚ[X] (RatFunc ℚ) X)
    (hy : PellRegular L y) (hz : PellRegular L z) :
    z^2 + y^2*z + x^3 ≠ 2 := by
  change x * embed L = embed X at hx
  intro he
  let w := z+y^2
  have hzw : z*w = 2 - x^3 := by dsimp [w]; linear_combination he
  have eF : (z*w) * embed L ^ 3 = embed (2 * L ^ 3 - X ^ 3) := by
    rw [hzw, map_sub, map_mul, map_pow, map_pow, map_ofNat, ← hx]
    ring
  have nz : z*w ≠ 0 := by
    intro H
    rw [H, zero_mul] at eF
    have hzero := (RatFunc.algebraMap_injective ℚ) (by simpa [embed] using eF.symm :
      algebraMap ℚ[X] (RatFunc ℚ) (2*L^3-X^3) = algebraMap ℚ[X] (RatFunc ℚ) 0)
    have dF := cube_difference_degree_of_le hL.ne_zero (dX.trans dL.ge)
    simp [hzero,dL] at dF
  obtain ⟨m, A, dA, hA, eA⟩ := PellRegular.exists_reduced dL (left_ne_zero_of_mul nz) hz
  obtain ⟨n, B, dB, hB, eB⟩ := PellRegular.exists_reduced dL (right_ne_zero_of_mul nz)
    (PellRegular.add_sq dL hz hy)
  have ⟨ord, ma, nb⟩ := pell_factor_pole_orders (k := 1) hL dL (by decide)
    (by simpa using dX) dA dB hX hA hB hzw (by simpa using hx) eA eB
  have casesMN : (m = 0 ∧ n = 3) ∨ (m = 3 ∧ n = 0) := by omega
  rcases casesMN with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hsub : ¬ L ∣ B - A*L^3 := by
      rwa [dvd_sub_left (dvd_mul_of_dvd_right (dvd_pow_self L (by decide : 3 ≠ 0)) A)]
    apply odd_pole_not_square hL.prime dL hsub hy
    simp only [pow_zero,mul_one] at eA
    rw [map_sub, map_mul, map_pow, ← eB, ← eA]
    dsimp [w]; ring
  · have hsub : ¬ L ∣ B*L^3 - A := by
      rwa [dvd_sub_right (dvd_mul_of_dvd_right (dvd_pow_self L (by decide : 3 ≠ 0)) B)]
    apply odd_pole_not_square hL.prime dL hsub hy
    simp only [pow_zero,mul_one] at eB
    rw [map_sub, map_mul, map_pow, ← eB, ← eA]
    dsimp [w]; ring

private theorem pole_order_sub_of_lt {L A B C : ℚ[X]} {m n k : ℕ}
    {f g : RatFunc ℚ} (hp : Prime L) (hmn : m < n) (hB : ¬ L ∣ B) (hC : ¬ L ∣ C)
    (hf : f * embed L ^ m = embed A) (hg : g * embed L ^ n = embed B)
    (hd : (g-f) * embed L ^ k = embed C) : k = n := by
  have hpow : L ∣ A * L^(n-m) :=
    dvd_mul_of_dvd_right (dvd_pow_self _ (by omega : n-m ≠ 0)) _
  have hred : ¬ L ∣ B - A * L^(n-m) := by rwa [dvd_sub_left hpow]
  have hdiff : (g-f) * embed L ^ n = embed (B - A * L^(n-m)) := by
    rw [sub_mul, hg, map_sub, map_mul, map_pow, ← hf, mul_assoc, ← pow_add]
    rw [show m+(n-m) = n by omega]
  exact (pole_orders_eq hp hC hred (cross_multiply hd hdiff)).symm

/-- If x has pole order three, y has pole order three. The two factors z and z+y²
have pole orders three and six, in either order. The inputs are reduced fractions. -/
theorem pell_pole_three_orders {L X Y A B : ℚ[X]} {q m n : ℕ}
    {x y z : RatFunc ℚ} (hp : Irreducible L) (dL : L.natDegree = 2)
    (dX : X.natDegree ≤ 6) (dA : A.natDegree ≤ 2*m) (dB : B.natDegree ≤ 2*n)
    (hX : ¬ L ∣ X) (hY : ¬ L ∣ Y) (hA : ¬ L ∣ A) (hB : ¬ L ∣ B)
    (hx : x * algebraMap ℚ[X] (RatFunc ℚ) L ^ 3 = algebraMap ℚ[X] (RatFunc ℚ) X)
    (hy : y * algebraMap ℚ[X] (RatFunc ℚ) L ^ q = algebraMap ℚ[X] (RatFunc ℚ) Y)
    (hz : z * algebraMap ℚ[X] (RatFunc ℚ) L ^ m = algebraMap ℚ[X] (RatFunc ℚ) A)
    (hw : (z+y^2) * algebraMap ℚ[X] (RatFunc ℚ) L ^ n = algebraMap ℚ[X] (RatFunc ℚ) B)
    (he : z^2+y^2*z+x^3 = 2) : q = 3 ∧ ((m = 3 ∧ n = 6) ∨ (m = 6 ∧ n = 3)) := by
  have hzw : z * (z+y^2) = 2-x^3 := by linear_combination he
  obtain ⟨ord, ma, nb⟩ := pell_factor_pole_orders (k := 3) hp dL (by decide)
    dX dA dB hX hA hB hzw hx hz hw
  have hsq : y^2 * embed L ^ (q*2) = embed (Y^2) := by
    change y * embed L^q = embed Y at hy
    rw [map_pow, ← hy, pow_mul, mul_pow]
  have hcop : ¬ L ∣ Y^2 := fun h => hY (hp.prime.dvd_of_dvd_pow h)
  rcases lt_or_ge m n with h | h
  · have hd : (z+y^2-z) * embed L ^ (q*2) = embed (Y^2) := by simpa using hsq
    have := pole_order_sub_of_lt hp.prime h hB hcop hz hw hd
    omega
  · have hd : (z-(z+y^2)) * embed L ^ (q*2) = embed (-(Y^2)) := by
      simpa using congrArg Neg.neg hsq
    have hcop' : ¬ L ∣ -(Y^2) := by simpa using hcop
    have := pole_order_sub_of_lt hp.prime (show n < m by omega) hA hcop' hw hz hd
    omega

/-- With pole order four in x, the two factors of 2−x³ both have pole order six,
and y has pole order at most three. The fractions are in reduced form. -/
theorem pell_pole_four_orders {L X Y A B : ℚ[X]} {q m n : ℕ}
    {x y z : RatFunc ℚ} (hp : Irreducible L) (dL : L.natDegree = 2)
    (dX : X.natDegree ≤ 8) (dA : A.natDegree ≤ 2*m) (dB : B.natDegree ≤ 2*n)
    (hX : ¬ L ∣ X) (hY : ¬ L ∣ Y) (hA : ¬ L ∣ A) (hB : ¬ L ∣ B)
    (hx : x * algebraMap ℚ[X] (RatFunc ℚ) L ^ 4 = algebraMap ℚ[X] (RatFunc ℚ) X)
    (hy : y * algebraMap ℚ[X] (RatFunc ℚ) L ^ q = algebraMap ℚ[X] (RatFunc ℚ) Y)
    (hz : z * algebraMap ℚ[X] (RatFunc ℚ) L ^ m = algebraMap ℚ[X] (RatFunc ℚ) A)
    (hw : (z+y^2) * algebraMap ℚ[X] (RatFunc ℚ) L ^ n = algebraMap ℚ[X] (RatFunc ℚ) B)
    (he : z^2+y^2*z+x^3 = 2) : m = 6 ∧ n = 6 ∧ q ≤ 3 := by
  have hzw : z * (z+y^2) = 2-x^3 := by linear_combination he
  obtain ⟨ord, ma, nb⟩ := pell_factor_pole_orders (k := 4) hp dL (by decide)
    dX dA dB hX hA hB hzw hx hz hw
  have nonconstant : ¬ ∃ c : ℚ, x = RatFunc.C c := by
    rintro ⟨c,rfl⟩
    have eq : C c * L^4 = X := by
      apply RatFunc.algebraMap_injective ℚ
      simpa only [map_mul, map_pow, RatFunc.algebraMap_C] using hx
    exact hX (eq ▸ dvd_mul_of_dvd_right (dvd_pow_self L (by decide : 4 ≠ 0)) _)
  have hm : m ≠ 0 := by
    rintro rfl
    apply nonconstant (constant_x_of_constant_fiber he (.inr (.inl ⟨A.coeff 0, ?_⟩)))
    have h := eq_C_of_natDegree_eq_zero (show A.natDegree = 0 by omega)
    calc z = embed A := by simpa using hz
         _ = embed (C (A.coeff 0)) := congrArg embed h
         _ = _ := RatFunc.algebraMap_C _
  have hn : n ≠ 0 := by
    rintro rfl
    apply nonconstant (constant_x_of_constant_fiber he (.inr (.inr ⟨B.coeff 0, ?_⟩)))
    have h := eq_C_of_natDegree_eq_zero (show B.natDegree = 0 by omega)
    calc z+y^2 = embed B := by simpa using hw
         _ = embed (C (B.coeff 0)) := congrArg embed h
         _ = _ := RatFunc.algebraMap_C _
  have hsq : y^2 * embed L ^ (q*2) = embed (Y^2) := by
    change y * embed L^q = embed Y at hy
    rw [map_pow, ← hy, pow_mul, mul_pow]
  have hcop : ¬ L ∣ Y^2 := fun h => hY (hp.prime.dvd_of_dvd_pow h)
  have same : m = n := by
    rcases lt_trichotomy m n with h | h | h
    · have hd : (z+y^2-z) * embed L ^ (q*2) = embed (Y^2) := by simpa using hsq
      have := pole_order_sub_of_lt hp.prime h hB hcop hz hw hd
      omega
    · exact h
    · have hd : (z-(z+y^2)) * embed L ^ (q*2) = embed (-(Y^2)) := by
        simpa using congrArg Neg.neg hsq
      have := pole_order_sub_of_lt hp.prime h hA (by simpa using hcop) hw hz hd
      omega
  refine ⟨by omega, by omega, ?_⟩
  by_contra high
  have sqneg : (-y^2) * embed L ^ (q*2) = embed (-(Y^2)) := by
    simpa using congrArg Neg.neg hsq
  have hdiff : (-y^2-z) * embed L ^ n = embed (-B) := by
    rw [map_neg, ← hw]; ring
  have := pole_order_sub_of_lt hp.prime (show m < q*2 by omega)
    (by simpa using hcop) (by simpa using hB) hz sqneg hdiff
  omega

/-- Polynomial substitutions in regular coordinates stay regular. -/
theorem PellRegular.aeval {ι : Type*} {L : ℚ[X]} (dL : L.natDegree = 2)
    (f : ι → RatFunc ℚ) (hf : ∀ i, PellRegular L (f i)) (P : MvPolynomial ι ℚ) :
    PellRegular L (MvPolynomial.aeval f P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    refine ⟨0,C c, by simp, ?_⟩
    rw [MvPolynomial.aeval_C, pow_zero, mul_one]
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) c
  | add p q hp hq =>
    obtain ⟨a,A,da,ea⟩ := hp
    obtain ⟨b,B,db,eb⟩ := hq
    refine ⟨a+b,A*L^b+B*L^a, ?_, ?_⟩
    · apply (natDegree_add_le _ _).trans
      apply max_le <;> apply natDegree_mul_le.trans <;> rw [natDegree_pow, dL] <;> omega
    · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← ea, ← eb, pow_add]
      ring
  | mul_X p i hp =>
    obtain ⟨a,A,da,ea⟩ := hp
    obtain ⟨b,B,db,eb⟩ := hf i
    refine ⟨a+b,A*B, natDegree_mul_le.trans (by omega), ?_⟩
    rw [map_mul, MvPolynomial.aeval_X, map_mul, ← ea, ← eb, pow_add]
    ring

/-- A concrete Pell parametrization. Any nonconstant affine function of the two
coordinates has the displayed form c + (a + bt)/(t² − D); arbitrary polynomials
in the Pell coordinates are allowed for the second and third surface coordinates. -/
theorem no_pell_affine_x (D a b c : ℚ) (hD : ¬ IsSquare D) (hn : a ≠ 0 ∨ b ≠ 0)
    (Y Z : MvPolynomial (Fin 2) ℚ) :
    let L : ℚ[X] := X^2 - C D
    let E := algebraMap ℚ[X] (RatFunc ℚ)
    let coords := ![E (X^2 + C D) / E L, E (C 2 * X) / E L]
    let x := E (C c) + E (C a + C b * X) / E L
    let y := MvPolynomial.aeval coords Y
    let z := MvPolynomial.aeval coords Z
    z^2 + y^2*z + x^3 ≠ 2 := by
  let L : ℚ[X] := X^2 - C D
  let U : ℚ[X] := X^2 + C D
  let V : ℚ[X] := C 2 * X
  let W : ℚ[X] := C a + C b * X
  let f : Fin 2 → RatFunc ℚ := ![embed U / embed L, embed V / embed L]
  have dl : L.natDegree = 2 := natDegree_X_pow_sub_C D
  have hp : Irreducible L := irreducible_X_pow_sub_C_of_prime Nat.prime_two
    (fun t h => hD ⟨t, by simpa [pow_two] using h.symm⟩)
  have el : embed L ≠ 0 := RatFunc.algebraMap_ne_zero hp.ne_zero
  have dw : W.natDegree ≤ 1 := (natDegree_add_le _ _).trans
    (max_le (by simp) ((natDegree_C_mul_le _ _).trans (by simp)))
  have nw : W ≠ 0 := by
    intro h
    have ha := congrArg (fun p : ℚ[X] => p.coeff 0) h
    have hb := congrArg (fun p : ℚ[X] => p.coeff 1) h
    simp [W] at ha hb
    exact hn.elim (· ha) (· hb)
  have reg : ∀ i, PellRegular L (f i) := by
    intro i
    fin_cases i
    · exact ⟨1,U, natDegree_X_pow_add_C.le, by simpa [f] using div_mul_cancel₀ (embed U) el⟩
    · exact ⟨1,V, (natDegree_C_mul_le _ _).trans (by simp),
        by simpa [f] using div_mul_cancel₀ (embed V) el⟩
  apply no_pell_pole_one_x (X := C c * L + W) hp dl
  · exact (natDegree_add_le _ _).trans
      (max_le ((natDegree_C_mul_le _ _).trans dl.le) (by omega))
  · rw [dvd_add_right (dvd_mul_left L (C c))]
    exact fun h => by have := natDegree_le_of_dvd h nw; omega
  · change (embed (C c) + embed W / embed L) * embed L = embed (C c * L + W)
    simp only [add_mul, div_mul_cancel₀ _ el, map_add, map_mul]
  · exact PellRegular.aeval dl f reg Y
  · exact PellRegular.aeval dl f reg Z

end SmallCubic
