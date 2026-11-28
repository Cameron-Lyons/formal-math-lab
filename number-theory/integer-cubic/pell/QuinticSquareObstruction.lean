module

public import PoleOne
import all PoleOne
public import QuinticFactor
import Mathlib.Tactic.Ring

public section
namespace SmallCubic.QuinticSquareObstruction
open Polynomial

private noncomputable abbrev E := algebraMap ℚ[X] (RatFunc ℚ)

private def Bound (L : ℚ[X]) (f : RatFunc ℚ) (n : ℕ) : Prop :=
  ∃ A, f * E L ^ n = E A

private def Pole (L : ℚ[X]) (f : RatFunc ℚ) (n : ℕ) : Prop :=
  ∃ A, ¬ L ∣ A ∧ f * E L ^ n = E A

private theorem Pole.bound {L f n} (h : Pole L f n) : Bound L f n :=
  let ⟨A,_,eq⟩ := h; ⟨A,eq⟩

private theorem Pole.ne_zero {L f n} (h : Pole L f n) : f ≠ 0 := by
  obtain ⟨A,ha,e⟩ := h
  rintro rfl
  have hA := RatFunc.algebraMap_injective ℚ (show E A = E 0 by simpa using e.symm)
  exact ha (hA ▸ dvd_zero L)

private theorem Pole.le_of_bound {L f m n} (hm : Pole L f m) (hn : Bound L f n) : m ≤ n := by
  obtain ⟨A,ha,ea⟩ := hm
  obtain ⟨B,eb⟩ := hn
  by_contra! h
  have e : A = B*L^(m-n) := by
    apply RatFunc.algebraMap_injective ℚ
    change E A = E _
    rw [map_mul,map_pow,← eb,← ea,mul_assoc,← pow_add,Nat.add_sub_of_le h.le]
  exact ha (e ▸ dvd_mul_of_dvd_right (dvd_pow_self L (by omega : m-n ≠ 0)) B)

private theorem Pole.mul {L f g m n} (hp : Prime L) (h : Pole L f m) (h' : Pole L g n) :
    Pole L (f*g) (m+n) := by
  obtain ⟨A,ha,ea⟩ := h
  obtain ⟨B,hb,eb⟩ := h'
  refine ⟨A*B,fun hd => (hp.dvd_mul.mp hd).elim ha hb,?_⟩
  rw [map_mul,← ea,← eb,pow_add]; ring

private theorem Pole.pow {L f m} (hp : Prime L) (h : Pole L f m) (d : ℕ) :
    Pole L (f^d) (m*d) := by
  obtain ⟨A,ha,ea⟩ := h
  refine ⟨A^d,fun hd => ha (hp.dvd_of_dvd_pow hd),?_⟩
  rw [map_pow,← ea,pow_mul,mul_pow]

private theorem Pole.add_lower {L f g m n} (h : Pole L f m) (h' : Bound L g n) (hlt : n < m) :
    Pole L (f+g) m := by
  obtain ⟨A,ha,ea⟩ := h
  obtain ⟨B,eb⟩ := h'
  have hd := dvd_mul_of_dvd_right (dvd_pow_self L (by omega : m-n ≠ 0)) B
  refine ⟨A+B*L^(m-n),by rwa [dvd_add_left hd],?_⟩
  rw [add_mul,ea,map_add,map_mul,map_pow,← eb,mul_assoc,← pow_add,Nat.add_sub_of_le hlt.le]

private theorem pole_const {L : ℚ[X]} (dL : L.natDegree=2) (c : ℚ) (hc : c≠0) :
    Pole L (c : RatFunc ℚ) 0 := by
  refine ⟨C c,?_,?_⟩
  · intro h
    have hdeg := natDegree_le_of_dvd h (C_ne_zero.mpr hc)
    simp [dL] at hdeg
  · simp only [pow_zero,mul_one]
    calc
      (c : RatFunc ℚ) = algebraMap ℚ (RatFunc ℚ) c := by simp
      _ = _ := IsScalarTower.algebraMap_apply ℚ ℚ[X] (RatFunc ℚ) c

/-- A product of two nonzero Pell-regular functions cannot have a smaller
pole order than their difference. -/
private theorem product_gap {L : ℚ[X]} (hp : Irreducible L) (dL : L.natDegree=2)
    {u v : RatFunc ℚ} (hu : PellRegular L u) (hv : PellRegular L v) {s d : ℕ}
    (hs : Pole L (u*v) s) (hd : Pole L (v-u) d) : d ≤ s := by
  have hn := hs.ne_zero
  obtain ⟨i,A,_,ha,ea⟩ := hu.exists_reduced dL (left_ne_zero_of_mul hn)
  obtain ⟨j,B,_,hb,eb⟩ := hv.exists_reduced dL (right_ne_zero_of_mul hn)
  have hu' : Pole L u i := ⟨A,ha,ea⟩
  have hv' : Pole L v j := ⟨B,hb,eb⟩
  have hij := (hu'.mul hp.prime hv').le_of_bound hs.bound
  apply le_trans (b := i+j) _ hij
  apply hd.le_of_bound
  refine ⟨B*L^i-A*L^j,?_⟩
  change u * E L ^ i = E A at ea
  change v * E L ^ j = E B at eb
  rw [map_sub,map_mul,map_mul,map_pow,map_pow,← ea,← eb,pow_add]; ring

/-- On a nonsplit Pell conic, the quintic lift x = r - p² z with
a z = 2 - r³ cannot solve the surface equation when r and p each have
simple poles and y is regular away from the two boundary points. -/
theorem no_negative_square_lift {L R P : ℚ[X]} (hL : Irreducible L) (dL : L.natDegree=2)
    (dR : R.natDegree ≤ 2) (dP : P.natDegree ≤ 2) (hR : ¬ L ∣ R) (hP : ¬ L ∣ P)
    (a : ℚ) (ha : a ≠ 0) {r p z y : RatFunc ℚ}
    (hr : r * algebraMap ℚ[X] (RatFunc ℚ) L = algebraMap ℚ[X] (RatFunc ℚ) R)
    (hp : p * algebraMap ℚ[X] (RatFunc ℚ) L = algebraMap ℚ[X] (RatFunc ℚ) P)
    (hz : (a : RatFunc ℚ)*z=2-r^3) (hy : PellRegular L y) :
    z^2+y^2*z+(r-p^2*z)^3 ≠ 2 := by
  intro he
  have rr : Pole L r 1 := ⟨R,hR,by simpa using hr⟩
  have pp : Pole L p 1 := ⟨P,hP,by simpa using hp⟩
  have rrreg : PellRegular L r := ⟨1,R,dR,by simpa using hr⟩
  have ppreg : PellRegular L p := ⟨1,P,dP,by simpa using hp⟩
  have hpr := hL.prime
  have ainv : (a : RatFunc ℚ) ≠ 0 := by exact_mod_cast ha
  have ze : z = ((a⁻¹ : ℚ) : RatFunc ℚ)*((-1)*r^3+2) := by
    push_cast
    field_simp [ainv]
    linear_combination hz
  have zz : Pole L z 3 := by
    rw [ze]
    convert (pole_const dL a⁻¹ (inv_ne_zero ha)).mul hpr
      (((pole_const dL (-1) (by decide)).mul hpr (rr.pow hpr 3)).add_lower
        (pole_const dL 2 (by decide)).bound (by decide)) using 1
    norm_num
  let coords : Fin 3 → RatFunc ℚ := ![r,p,y]
  have hreg : ∀ i, PellRegular L (coords i) := by
    intro i
    fin_cases i
    · exact rrreg
    · exact ppreg
    · exact hy
  let Xr := MvPolynomial.X (R := ℚ) (0 : Fin 3)
  let Xp := MvPolynomial.X (R := ℚ) (1 : Fin 3)
  let Xy := MvPolynomial.X (R := ℚ) (2 : Fin 3)
  let Z := MvPolynomial.C a⁻¹ * ((-1)*Xr^3+2)
  let u := 2*y-2*p^3*z+3*r*p
  let v := 2*y+2*p^3*z-3*r*p
  have ureg : PellRegular L u := by
    convert PellRegular.aeval dL coords hreg (2*Xy-2*Xp^3*Z+3*Xr*Xp) using 1
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_neg,Z,Xr,Xp,Xy,
      MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    simp [u,coords,ze]
  have vreg : PellRegular L v := by
    convert PellRegular.aeval dL coords hreg (2*Xy+2*Xp^3*Z-3*Xr*Xp) using 1
    simp only [map_add,map_sub,map_mul,map_pow,map_ofNat,map_neg,Z,Xr,Xp,Xy,
      MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    simp [v,coords,ze]
  have hprod : u*v=4*((a : RatFunc ℚ)-z)+3*r^2*p^2 := by
    apply QuinticFactor.negative_square_remainder
    apply sub_eq_zero.mp
    apply (mul_eq_zero.mp _).resolve_left zz.ne_zero
    have h := QuinticFactor.substitution (a : RatFunc ℚ) r (-p^2) z y hz
    linear_combination he - h
  have rem : Pole L (u*v) 4 := by
    rw [hprod,show 4*((a : RatFunc ℚ)-z)+3*r^2*p^2 =
      3*r^2*p^2+((-4)*z+(4*a : ℚ)) by push_cast; ring]
    convert (((pole_const dL 3 (by decide)).mul hpr (rr.pow hpr 2)).mul hpr (pp.pow hpr 2)).add_lower
      (((pole_const dL (-4) (by decide)).mul hpr zz).add_lower
        (pole_const dL (4*a) (mul_ne_zero (by decide) ha)).bound (by decide)).bound (by decide) using 1
    norm_num
  have diff : Pole L (v-u) 6 := by
    rw [show v-u=4*p^3*z+(-6)*r*p by dsimp [v,u]; ring]
    convert (((pole_const dL 4 (by decide)).mul hpr (pp.pow hpr 3)).mul hpr zz).add_lower
      (((pole_const dL (-6) (by decide)).mul hpr rr).mul hpr pp).bound (by decide) using 1
    norm_num
  have := product_gap hL dL ureg vreg rem diff
  omega

end SmallCubic.QuinticSquareObstruction
