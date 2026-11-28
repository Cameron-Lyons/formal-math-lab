module

public import PoleTwoLifting
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-! The reflection and endpoint obstruction for the cubic branches through
(1,0,1) on u²−2v²=1. The rational Mordell–Weil generator used to interpret
the finite-group computation is recorded in Cremona's data for 1728a1. -/
public section
namespace SmallCubic.CubicEndpoint

open Polynomial
abbrev Index := Fin 3 × Fin 6

variable {R : Type*} [CommRing R]

/-- A degree-six numerator with prescribed constant term. -/
noncomputable def numerator (d : R) (a : Fin 6 → R) : R[X] :=
  C d + ∑ j, C (a j) * X^(j.val+1)

/-- Reflect t to −t, with the additional sign change in the y coordinate. -/
def reflect (a : Index → R) (i : Index) : R :=
  (if i.1 = 1 then -1 else 1) * (-1 : R)^(i.2.val+1) * a i

private theorem reflect_num (sg d : R) (a : Fin 6 → R) :
    numerator (sg*d) (fun j => sg*(-1)^(j.val+1)*a j) =
      C sg * (numerator d a).comp (-X) := by
  simp only [numerator, add_comp, C_comp, sum_comp, mul_comp, pow_comp, X_comp, mul_add,
    Finset.mul_sum, map_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show (-X : R[X]) = C (-1) * X by simp, mul_pow, ← map_pow]
  ring

noncomputable def residual (a : Index → R) : R[X] :=
  let Xn := numerator 1 (fun j => a (0,j))
  let Yn := numerator 0 (fun j => a (1,j))
  let Zn := numerator 1 (fun j => a (2,j))
  let L := 1-2*Polynomial.X^2
  Xn^3+Zn*Yn^2+Zn^2*L^3-2*L^9

private theorem residual_reflect (a : Index → R) :
    residual (reflect a) = (residual a).comp (-X) := by
  have hX := reflect_num (1:R) 1 (fun j => a (0,j))
  have hY := reflect_num (-1:R) 0 (fun j => a (1,j))
  have hZ := reflect_num (1:R) 1 (fun j => a (2,j))
  simp only [one_mul, mul_zero, map_one, map_neg, neg_one_mul] at hX hY hZ
  simp only [neg_mul] at hY
  simp [residual, reflect, hX, hY, hZ, sub_comp, pow_comp, mul_comp, add_comp]

noncomputable def system (R : Type*) [CommRing R] (i : Index) : MvPolynomial Index R :=
  (residual (R := MvPolynomial Index R) MvPolynomial.X).coeff (6*i.1.val+i.2.val+1)

private theorem eval_system (a : Index → R) (i : Index) :
    MvPolynomial.eval a (system R i) = (residual a).coeff (6*i.1.val+i.2.val+1) := by
  rw [system, ← Polynomial.coeff_map]
  simp [residual, numerator, Polynomial.map_sum, MvPolynomial.eval_X]

/-- A root matching its reflection modulo 7 is exactly reflection-symmetric
if the reduced Jacobian is nonsingular. In particular the top y coefficient
vanishes in characteristic zero. -/
theorem symmetry_and_zero_endpoint [IsDomain R] [CharZero R] (ρ : R →+* ZMod 7)
    (a : Index → R) (ha : residual a = 0)
    (hr : ∀ j, ρ (reflect a j) = ρ (a j))
    (hj : (Matrix.of fun i j => ρ (MvPolynomial.eval a
      (MvPolynomial.pderiv j (system R i)))).det ≠ 0) :
    reflect a = a ∧ a (1,5) = 0 := by
  have hf : ∀ i, MvPolynomial.eval (reflect a) (system R i) =
      MvPolynomial.eval a (system R i) := by
    intro i
    rw [eval_system, eval_system, residual_reflect, ha, zero_comp]
  have h := polynomial_system_lift_unique ρ (system R) (reflect a) a hr hf hj
  refine ⟨h, ?_⟩
  have he := congrFun h (1,5)
  have he' : -(a (1,5)) = a (1,5) := by
    change -(1:R) * (-1)^6 * a (1,5) = a (1,5) at he
    norm_num at he
    exact he
  have ht : (2:R)*a (1,5) = 0 := by linear_combination -he'
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The coefficient of degree eighteen at the endpoint after y₆ vanishes.
Here −8 is the leading coefficient of L³. -/
theorem endpoint_curve (x z : ℚ) (h : x^3 - 8*z^2 = -1024) :
    (z / (-8))^2 = (-(x / (-8)))^3 + 2 := by linear_combination (-1/512 : ℚ)*h

private theorem numerator_bound (d : R) (a : Fin 6 → R) :
    (numerator d a).natDegree ≤ 6 := by
  apply natDegree_add_le_of_le (m := 6) (n := 6) (by simp)
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_le _ _).trans ((natDegree_X_pow_le _).trans (by omega))

private theorem numerator_top (d : R) (a : Fin 6 → R) :
    (numerator d a).coeff 6 = a 5 := by
  simp [numerator, Fin.sum_univ_succ]

/-- Extract the degree-eighteen coefficient of the surface identity at
t = ∞. Its affine coordinates use the leading denominator −8. -/
theorem residual_endpoint (a : Index → ℚ) (ha : residual a = 0) (hy : a (1,5) = 0) :
    (a (2,5) / (-8))^2 = (-(a (0,5) / (-8)))^3 + 2 := by
  apply endpoint_curve
  let x := numerator 1 (fun j => a (0,j))
  let y := numerator 0 (fun j => a (1,j))
  let z := numerator 1 (fun j => a (2,j))
  let L : ℚ[X] := 1-2*X^2
  have hx : x.natDegree ≤ 6 := numerator_bound ..
  have hy' : y.natDegree ≤ 6 := numerator_bound ..
  have hz : z.natDegree ≤ 6 := numerator_bound ..
  have hL : L.natDegree ≤ 2 := by
    apply natDegree_sub_le_of_le (m := 2) (n := 2) (by simp)
    exact natDegree_mul_le.trans (by simp)
  have h2 : L.coeff 2 = -2 := by
    have h1 : (1 : ℚ[X]).coeff 2 = 0 := coeff_eq_zero_of_natDegree_lt (by simp)
    dsimp [L]
    rw [h1, coeff_ofNat_mul, coeff_X_pow]
    norm_num
  have h := congrArg (fun p : ℚ[X] => p.coeff 18) ha
  change (x^3+z*y^2+z^2*L^3-2*L^9).coeff 18 = 0 at h
  rw [coeff_sub, coeff_add, coeff_add, coeff_ofNat_mul,
      coeff_pow_of_natDegree_le (m := 3) hx,
      coeff_mul_add_eq_of_natDegree_le (df := 6) (dg := 12) hz (natDegree_pow_le.trans (by omega)),
      coeff_mul_add_eq_of_natDegree_le (df := 12) (dg := 6)
        (natDegree_pow_le.trans (by omega)) (natDegree_pow_le.trans (by omega)),
      coeff_pow_of_natDegree_le (m := 2) hy', coeff_pow_of_natDegree_le (m := 2) hz,
      coeff_pow_of_natDegree_le (m := 3) hL, coeff_pow_of_natDegree_le (m := 9) hL, h2] at h
  simp [x,y,z,numerator_top,hy] at h
  linarith

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

theorem endpoint_residues (x z : ZMod 7) (hx : x=0) (hz : z=4) :
    -(x/(-8))=0 ∧ z/(-8)=3 := by
  subst x; subst z
  refine ⟨by simp, (div_eq_iff (by decide : (-8 : ZMod 7) ≠ 0)).mpr (by decide)⟩

def curve : WeierstrassCurve.Affine (ZMod 7) := ⟨0,0,0,0,2⟩

def generator : curve.Point := .some 6 1 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  decide)

def endpoint : curve.Point := .some 0 3 (by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff]
  decide)

/-- Good reduction of any rational multiple of (−1,1) cannot be (0,3). -/
theorem endpoint_not_multiple (n : ℤ) : n • generator ≠ endpoint := by
  have h3 : (3:ℤ) • generator = 0 := by decide +kernel
  have hh : n • generator = (n%3) • generator := by
    conv_lhs => rw [show n = n%3 + (n/3)*3 by omega]
    rw [add_zsmul, mul_zsmul, h3, zsmul_zero, add_zero]
  rw [hh]
  have h : n%3 = 0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases h with h | h | h <;> rw [h] <;> decide +kernel

end SmallCubic.CubicEndpoint
