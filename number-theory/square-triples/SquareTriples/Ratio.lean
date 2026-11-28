import SquareTriples.Determinant

namespace SquareTriples

/-- Enumerate possible partners by their square root. -/
private def partners (fixed lo : Nat) : List Nat :=
  (List.range ((fixed*(1000*lo)+1).sqrt+1)).filterMap fun r =>
    let n := r*r-1
    if n % fixed = 0 ∧ lo < n/fixed then some (n/fixed) else none

private theorem mem_partners {fixed lo n : Nat} (hf : 0 < fixed)
    (hlo : lo < n) (hhi : n ≤ 1000*lo) (h : Edge fixed n) :
    n ∈ partners fixed lo := by
  obtain ⟨r, hr⟩ := h
  have cap := Nat.mul_le_mul_left fixed hhi
  have root := Nat.mul_self_lt_mul_self_iff.mp <|
    Nat.lt_of_le_of_lt (show r*r ≤ fixed*(1000*lo)+1 by omega) (Nat.lt_succ_sqrt _)
  apply List.mem_filterMap.mpr
  exact ⟨r, List.mem_range.mpr root, by simp [show r*r-1 = fixed*n by omega,
    Nat.mul_div_cancel_left _ hf, hlo]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 1024 in
/-- For each possible smallest pair, check the middle pair against the height
bound. For each surviving pair, check the three remaining edges. -/
private theorem finite_cases :
    ∀ a ∈ List.range' 1 24, ∀ x ∈ List.range' 1 24, a*x < 25 → Edge a x →
    ∀ b ∈ partners x a, ∀ y ∈ partners a x, 64*(a*x)^2*(b*y+1) < 1000000 → Edge b y →
    ∀ c ∈ partners x a, b < c → Edge c y →
    ∀ z ∈ partners a x, y < z → Edge b z → ¬ Edge c z := by
  decide +kernel

/-- Write p for the product of the smallest labels and q for the product of
the middle labels. Cancel p from the height bound. If p ≥ 25, its left side
is at least 64 · 25² · 26 = 1,040,000. -/
private theorem corner_bounds {p q top : Nat} (order : p ≤ q)
    (height : 64*p^3*(q+1) < top) (cap : top ≤ 1000000*p) :
    p < 25 ∧ 64*p^2*(q+1) < 1000000 := by
  have eq : 64*p^3*(q+1) = (64*p^2*(q+1))*p := by grind
  rw [eq] at height
  have bound := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_lt_of_le height cap)
  refine ⟨?_, bound⟩
  by_cases large : 25 ≤ p
  · have lower := Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left large 2))
        (show 26 ≤ q+1 by omega)
    omega
  · omega

/-- Under both proposed ratio bounds, the determinant forces the two smallest
labels to have product below 25. The finite check then excludes the solution. -/
theorem ordered_solution_ratio_1000 {a b c x y z : Nat}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (sol : Solution a b c x y z) : 1000*a < c ∨ 1000*x < z := by
  apply Classical.byContradiction
  intro limits
  simp only [not_or, Nat.not_lt] at limits
  have top : c*z ≤ 1000000*(a*x) := calc
    c*z ≤ (1000*a)*(1000*x) := Nat.mul_le_mul limits.1 limits.2
    _ = 1000000*(a*x) := by grind
  have order := Nat.mul_le_mul (Nat.le_of_lt hab) (Nat.le_of_lt hxy)
  obtain ⟨small, middle⟩ := corner_bounds order
    (ordered_solution_height_gap hab hbc hxy hyz sol) top
  obtain ⟨positive, _, edges⟩ := sol
  simp at positive edges
  obtain ⟨⟨ax,ay,az⟩,⟨bx,by',bz⟩,cx,cy,cz⟩ := edges
  have ha : 0 < a := by omega
  have hx : 0 < x := by omega
  have a24 : a ∈ List.range' 1 24 := by
    have := Nat.le_mul_of_pos_right a hx
    simp [List.mem_range'_1]; omega
  have x24 : x ∈ List.range' 1 24 := by
    have := Nat.le_mul_of_pos_left x ha
    simp [List.mem_range'_1]; omega
  exact finite_cases a a24 x x24 small ax
    b (mem_partners hx hab (by omega) bx.symm) y (mem_partners ha hxy (by omega) ay) middle by'
    c (mem_partners hx (Nat.lt_trans hab hbc) limits.1 cx.symm) hbc cy
    z (mem_partners ha (Nat.lt_trans hxy hyz) limits.2 az) hyz bz cz

/-- Each of the triples may lie at a different scale. At least one contains a
pair whose larger entry exceeds 1000 times the smaller entry. -/
theorem solution_ratio_1000 {a b c x y z : Nat} (sol : Solution a b c x y z) :
    (∃ i ∈ [a,b,c], ∃ j ∈ [a,b,c], 1000*i < j) ∨
    (∃ i ∈ [x,y,z], ∃ j ∈ [x,y,z], 1000*i < j) := by
  obtain ⟨A,hA,B,_,C,hC,X,hX,Y,_,Z,hZ,ab,bc,xy,yz,sorted⟩ := ordered_solution_sides sol
  rcases ordered_solution_ratio_1000 ab bc xy yz sorted with h | h
  · exact Or.inl ⟨A,hA,C,hC,h⟩
  · exact Or.inr ⟨X,hX,Z,hZ,h⟩

end SquareTriples
