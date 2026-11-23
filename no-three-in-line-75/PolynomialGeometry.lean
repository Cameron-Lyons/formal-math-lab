import Grid75

/-! Polynomial constructions on the 75 by 75 grid.

Coordinates are canonical representatives in {0,…,74}. Polynomial evaluation
uses arithmetic modulo 75. Collinearity is tested over the integers by
`Grid75.det`.

Adding 15 times a parameter moves along a modular affine line because
15 squared vanishes modulo 75. In the five possible parameter lifts, some
three line points have ordinary zero determinant. -/

namespace Grid75.ModularCurve

abbrev Z75 := Fin 75

namespace Polynomial

/-- Coefficients in increasing powers, evaluated by Horner's rule. -/
def evalAt {n : Nat} [NeZero n] : List (Fin n) → Fin n → Fin n
  | [], _ => 0
  | a :: p, x => a + x * evalAt p x

def slopeAt {n : Nat} [NeZero n] : List (Fin n) → Fin n → Fin n
  | [], _ => 0
  | _ :: p, x => evalAt p x + x * slopeAt p x

/-- The linear term of Taylor's formula is exact when the increment squares to zero. -/
theorem first_order {n : Nat} [NeZero n] (p : List (Fin n)) (x h j : Fin n) (nilpotent : h*h = 0) :
    evalAt p (x + h*j) = evalAt p x + h*j*slopeAt p x := by
  induction p with
  | nil => simp only [evalAt, slopeAt]; grind
  | cons a p ih => simp only [evalAt, slopeAt, ih]; grind

end Polynomial

abbrev evaluate : List Z75 → Z75 → Z75 := Polynomial.evalAt

def point (p q : List Z75) (t : Z75) : Point := (evaluate p t, evaluate q t)

private def as75 (j : Fin 5) : Z75 := ⟨j.val, by omega⟩
private def lowSlope (a : Z75) : Fin 5 := Fin.ofNat 5 a.val
private def highDigit (a : Z75) : Fin 5 := Fin.ofNat 5 (a.val / 15)

/-- Ordinary integer coordinates of a modular affine function on five lifts. -/
private theorem digit_formula : ∀ (a d : Z75) (j : Fin 5),
    (a + 15 * as75 j * d).val =
      a.val % 15 + 15 * (highDigit a + lowSlope d * j).val := by
  set_option maxRecDepth 10000 in decide +kernel

private def determinant (x y u v w z : Int) : Int := (u-x)*(z-y)-(v-y)*(w-x)

private theorem five_line : ∀ a b u v : Fin 5, ∃ i j k : Fin 5, i < j ∧ j < k ∧
    determinant ((a+u*i).val : Int) ((b+v*i).val : Int)
      ((a+u*j).val : Int) ((b+v*j).val : Int) ((a+u*k).val : Int) ((b+v*k).val : Int) = 0 := by
  set_option maxRecDepth 10000 in decide +kernel

private def affine (x y u v : Z75) (j : Fin 5) : Point :=
  (x + 15 * as75 j * u, y + 15 * as75 j * v)

private theorem affine_triple (x y u v : Z75) :
    ∃ i j k : Fin 5, i < j ∧ j < k ∧
      det (affine x y u v i) (affine x y u v j) (affine x y u v k) = 0 := by
  obtain ⟨i, j, k, hij, hjk, h⟩ :=
    five_line (highDigit x) (highDigit y) (lowSlope u) (lowSlope v)
  refine ⟨i, j, k, hij, hjk, ?_⟩
  simp only [det, affine, digit_formula, Int.natCast_add, Int.natCast_mul]
  dsimp only [determinant] at h
  grind

/-- Coefficients of powers of y, where each coefficient is a polynomial in x. -/
def evaluate₂ : List (List Z75) → Z75 → Z75 → Z75
  | [], _, _ => 0
  | a :: p, x, y => evaluate a x + y * evaluate₂ p x y

private def partialX : List (List Z75) → Z75 → Z75 → Z75
  | [], _, _ => 0
  | a :: p, x, y => Polynomial.slopeAt a x + y * partialX p x y

private def partialY : List (List Z75) → Z75 → Z75 → Z75
  | [], _, _ => 0
  | _ :: p, x, y => evaluate₂ p x y + y * partialY p x y

private theorem plane_taylor (p : List (List Z75)) (x y u v j : Z75) :
    evaluate₂ p (x + 15 * j * u) (y + 15 * j * v) =
      evaluate₂ p x y + 15 * j * (u * partialX p x y + v * partialY p x y) := by
  induction p with
  | nil => simp only [evaluate₂, partialX, partialY]; grind
  | cons a p ih =>
    simp only [evaluate₂, partialX, partialY, ih]
    have nilpotent : (15 : Z75) * 15 = 0 := by decide
    have ha := Polynomial.first_order a x 15 (j*u) nilpotent
    grind

private theorem tangent_direction : ∀ a b : Z75, ∃ u v : Fin 5,
    (u ≠ 0 ∨ v ≠ 0) ∧ (15 : Z75) * (as75 u * a + as75 v * b) = 0 := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem lift_injective : ∀ (x : Z75) (u : Fin 5), u ≠ 0 →
    ∀ i j : Fin 5, x + 15 * as75 i * as75 u = x + 15 * as75 j * as75 u → i = j := by
  set_option maxRecDepth 10000 in decide +kernel

/-- Every nonempty zero locus of a single polynomial modulo 75 contains three
distinct points collinear in the ordinary integer grid. -/
theorem zero_locus_triple (p : List (List Z75)) {x y : Z75} (root : evaluate₂ p x y = 0) :
    ∃ a b c : Point, [a, b, c].Nodup ∧ det a b c = 0 ∧
      evaluate₂ p a.1 a.2 = 0 ∧ evaluate₂ p b.1 b.2 = 0 ∧ evaluate₂ p c.1 c.2 = 0 := by
  obtain ⟨u, v, nonzero, tangent⟩ := tangent_direction (partialX p x y) (partialY p x y)
  let f := affine x y (as75 u) (as75 v)
  obtain ⟨i, j, k, hij, hjk, hcol⟩ := affine_triple x y (as75 u) (as75 v)
  have allroot (l : Fin 5) : evaluate₂ p (f l).1 (f l).2 = 0 := by
    change evaluate₂ p (x + 15 * as75 l * as75 u) (y + 15 * as75 l * as75 v) = 0
    rw [plane_taylor, root]
    grind
  have inj (a b : Fin 5) (e : f a = f b) : a = b := by
    rcases nonzero with hu | hv
    · exact lift_injective x u hu a b (congrArg Prod.fst e)
    · exact lift_injective y v hv a b (congrArg Prod.snd e)
  refine ⟨f i, f j, f k, ?_, hcol, allroot i, allroot j, allroot k⟩
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, and_true]
  have hi : i.val < j.val := hij
  have hj : j.val < k.val := hjk
  grind

end Grid75.ModularCurve
