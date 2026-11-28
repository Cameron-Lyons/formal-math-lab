import SquareTriples.Basic

namespace SquareTriples

/-- A minor of the square-root matrix, together with its conjugate product. -/
private theorem minor_data {a b x y p q r s : Nat}
    (ha : a < b) (hx : x < y)
    (hp : p*p = a*x+1) (hq : q*q = a*y+1)
    (hr : r*r = b*x+1) (hs : s*s = b*y+1) :
    ∃ m, 0 < m ∧ p*s = q*r+m ∧ m*(p*s+q*r) = (b-a)*(y-x) ∧
      4*(a*x)*(m*m) < b*y ∧ 2*(a*x)*m < p*s := by
  generalize hd : b-a = d
  generalize hf : y-x = f
  have hb : b = a+d := by omega
  have hy : y = x+f := by omega
  have bal : (p*s)*(p*s) = (q*r)*(q*r)+d*f := by
    calc
      (p*s)*(p*s) = (p*p)*(s*s) := by ac_rfl
      _ = (q*q)*(r*r)+d*f := by rw [hp,hs,hq,hr,hb,hy]; grind
      _ = (q*r)*(q*r)+d*f := by ac_rfl
  have pos := Nat.mul_pos (show 0 < d by omega) (show 0 < f by omega)
  have inc : q*r < p*s := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  let m := p*s-q*r
  have hm : p*s = q*r + m := by dsimp [m]; omega
  have hpos : 0 < m := by omega
  have factor : m*(p*s+q*r) = d*f := by
    rw [hm] at bal ⊢
    have h : (q*r+m)*(q*r+m) = (q*r)*(q*r)+m*(q*r+m+q*r) := by grind
    omega
  refine ⟨m, hpos, hm, factor, ?_⟩
  have small := Nat.mul_lt_mul_of_pos_left (show 2*(q*r) < p*s+q*r by omega) hpos
  rw [factor] at small
  have cap : d*f ≤ b*y := Nat.mul_le_mul (by omega) (by omega)
  have step := Nat.mul_self_lt_mul_self (Nat.lt_of_lt_of_le small cap)
  have side : (a*x)*(b*y) ≤ (q*r)*(q*r) := by
    calc
      (a*x)*(b*y) = (a*y)*(b*x) := by ac_rfl
      _ ≤ (q*q)*(r*r) := Nat.mul_le_mul (by omega) (by omega)
      _ = (q*r)*(q*r) := by ac_rfl
  have last : (4*(a*x)*(m*m))*(b*y) < (b*y)*(b*y) := by
    calc
      (4*(a*x)*(m*m))*(b*y) = (4*(m*m))*((a*x)*(b*y)) := by ac_rfl
      _ ≤ (4*(m*m))*((q*r)*(q*r)) := Nat.mul_le_mul_left _ side
      _ = (m*(2*(q*r)))*(m*(2*(q*r))) := by grind
      _ < (b*y)*(b*y) := step
  have bound := Nat.lt_of_mul_lt_mul_right last
  refine ⟨bound, Nat.mul_self_lt_mul_self_iff.mp ?_⟩
  calc
    _ = (a*x)*(4*(a*x)*(m*m)) := by grind
    _ ≤ (a*x)*(b*y) := Nat.mul_le_mul_left _ (Nat.le_of_lt bound)
    _ < (p*p)*(s*s) := Nat.mul_lt_mul_of_lt_of_lt (by omega) (by omega)
    _ = _ := by ac_rfl

/-- Condensation converts the strict sign of the determinant into a gap
    of at least the center entry between two products of adjacent minors. -/
private theorem condensation {p q r s t u v w k A B C D : Nat}
    (hA : p*t = q*s+A) (hB : q*u = r*t+B)
    (hC : s*w = t*v+C) (hD : t*k = u*w+D)
    (h : A*D < B*C) : A*D+t ≤ B*C := by
  let positive := p*t*k+q*u*v+r*s*w
  let negative := r*t*v+q*s*k+p*u*w
  have id : B*C+t*positive = A*D+t*negative := by
    dsimp [positive, negative]
    grind
  have hp : positive < negative :=
    Nat.lt_of_mul_lt_mul_left (show t*positive < t*negative by omega)
  have inc := Nat.mul_le_mul_left t (show positive+1 ≤ negative from hp)
  rw [Nat.mul_add, Nat.mul_one] at inc
  omega

/-- For ordered row and column triples, the product of the two largest
    labels exceeds sixty-four times the cube of the product of the two
    smallest labels times the central square. -/
theorem ordered_edges_height_gap {a b c x y z : Nat}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (edges : ∀ i ∈ [a,b,c], ∀ j ∈ [x,y,z], Edge i j) : 64*(a*x)^3*(b*y+1) < c*z := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at edges
  obtain ⟨⟨⟨p,hp⟩,⟨q,hq⟩,⟨r,hr⟩⟩,⟨⟨s,hs⟩,⟨t,ht⟩,⟨u,hu⟩⟩,⟨v,hv⟩,⟨w,hw⟩,⟨k,hk⟩⟩ := edges
  -- In the root matrix with rows (p,q,r), (s,t,u), (v,w,k), the adjacent
  -- two-by-two minors are A,B in the first two rows and C,D in the last two.
  obtain ⟨A,hApos,hA,hAs,_⟩ := minor_data hab hxy hp hq hs ht
  obtain ⟨B,hBpos,hB,hBs,hBb,_⟩ := minor_data hab hyz hq hr ht hu
  obtain ⟨C,hCpos,hC,hCs,hCb,_⟩ := minor_data hbc hxy hs ht hv hw
  obtain ⟨D,hDpos,hD,hDs,_⟩ := minor_data hbc hyz ht hu hw hk
  -- Each adjacent minor times its conjugate is the product of its label gaps.
  -- Multiplying along either diagonal uses exactly the same four gaps.
  let X := (p*t+q*s)*(t*k+u*w)
  let Y := (q*u+r*t)*(s*w+t*v)
  have balanced : (A*D)*X = (B*C)*Y := by
    calc
      _ = (A*(p*t+q*s))*(D*(t*k+u*w)) := by dsimp [X]; ac_rfl
      _ = (B*(q*u+r*t))*(C*(s*w+t*v)) := by rw [hAs,hDs,hBs,hCs]; ac_rfl
      _ = _ := by dsimp [Y]; ac_rfl

  -- The conjugate products differ by a weighted sum of the three outer minors.
  have hac := Nat.lt_trans hab hbc
  obtain ⟨M,hMpos,hm,_,_,hM⟩ := minor_data hac (Nat.lt_trans hxy hyz) hp hr hv hk
  obtain ⟨N,_,hn,_,_,hN⟩ := minor_data hac hxy hp hq hv hw
  obtain ⟨O,_,ho,_,_,hO⟩ := minor_data hac hyz hq hr hw hk
  let E := (t*t)*M+(t*u)*N+(t*s)*O
  have diagonal : X = (t*t)*(p*k)+(t*u)*(p*w)+(t*s)*(q*k)+q*s*u*w := by dsimp [X]; grind
  have split : X = Y+E := by rw [diagonal, hm, hn, ho]; dsimp [Y,E]; grind
  have htpos : 0 < t := by cases t <;> simp_all
  have hE : 0 < E := by
    have := Nat.mul_pos (Nat.mul_pos htpos htpos) hMpos
    dsimp [E]; omega
  have order : A*D < B*C := Nat.lt_of_mul_lt_mul_right (calc
    (A*D)*Y < (A*D)*X := Nat.mul_lt_mul_of_pos_left (by omega) (Nat.mul_pos hApos hDpos)
    _ = (B*C)*Y := balanced)

  -- Condensation gives (AD + t)X ≤ BCX = ADX + BCE, hence tX ≤ BCE.
  have center := Nat.mul_le_mul_right X (condensation hA hB hC hD order)
  have expansion : (B*C)*X = (A*D)*X+(B*C)*E := by rw [balanced, ← Nat.mul_add, ← split]
  rw [Nat.add_mul, expansion] at center
  have centerBound : t*X ≤ (B*C)*E := by omega

  -- Each outer minor, multiplied by L, is smaller than its diagonal root product.
  let L := 2*(a*x)
  change L*M < p*k at hM
  change L*N < p*w at hN
  have outer : L*O < q*k := Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right O (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left a (Nat.le_of_lt hxy)))) hO
  have errorBound : L*E < X := by
    have h₁ := Nat.mul_lt_mul_of_pos_left hM (Nat.mul_pos htpos htpos)
    have h₂ := Nat.mul_le_mul_left (t*u) (Nat.le_of_lt hN)
    have h₃ := Nat.mul_le_mul_left (t*s) (Nat.le_of_lt outer)
    calc
      L*E = (t*t)*(L*M)+(t*u)*(L*N)+(t*s)*(L*O) := by dsimp [E]; grind
      _ < (t*t)*(p*k)+(t*u)*(p*w)+(t*s)*(q*k) := by omega
      _ ≤ (t*t)*(p*k)+(t*u)*(p*w)+(t*s)*(q*k)+q*s*u*w := Nat.le_add_right _ _
      _ = X := diagonal.symm
  have sharp : L*t < B*C := Nat.lt_of_mul_lt_mul_right (calc
    (L*t)*X = L*(t*X) := by ac_rfl
    _ ≤ L*((B*C)*E) := Nat.mul_le_mul_left L centerBound
    _ = (B*C)*(L*E) := by ac_rfl
    _ < (B*C)*X := Nat.mul_lt_mul_of_pos_left errorBound (Nat.mul_pos hBpos hCpos))
  have corner := Nat.mul_lt_mul_of_lt_of_lt hBb hCb
  have cap : (16*(a*x)*((B*C)*(B*C)))*(b*y) < (c*z)*(b*y) := by
    calc
      _ = (4*(a*y)*(B*B))*(4*(b*x)*(C*C)) := by grind
      _ < (b*z)*(c*y) := corner
      _ = _ := by ac_rfl
  have bound := Nat.lt_of_mul_lt_mul_right cap
  calc
    64*(a*x)^3*(b*y+1) = (16*(a*x))*((L*t)*(L*t)) := by rw [← ht]; dsimp [L]; grind
    _ ≤ (16*(a*x))*((B*C)*(B*C)) :=
      Nat.mul_le_mul_left _ (Nat.mul_self_le_mul_self (Nat.le_of_lt sharp))
    _ < c*z := bound

/-- Ordered solutions obey a height-dependent product bound. -/
theorem ordered_solution_height_gap {a b c x y z : Nat}
    (hab : a < b) (hbc : b < c) (hxy : x < y) (hyz : y < z)
    (sol : Solution a b c x y z) : 64*(a*x)^3*(b*y+1) < c*z :=
  ordered_edges_height_gap hab hbc hxy hyz sol.2.2

private theorem sorted_labels {a b c : Nat} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p ∈ [a,b,c], ∃ q ∈ [a,b,c], ∃ r ∈ [a,b,c], p < q ∧ q < r := by
  simp
  omega

/-- Reorder a solution into two increasing triples, preserving positivity,
    distinctness, and the nine square conditions. -/
theorem ordered_solution_sides {a b c x y z : Nat} (sol : Solution a b c x y z) :
    ∃ A ∈ [a,b,c], ∃ B ∈ [a,b,c], ∃ C ∈ [a,b,c],
    ∃ X ∈ [x,y,z], ∃ Y ∈ [x,y,z], ∃ Z ∈ [x,y,z],
    A < B ∧ B < C ∧ X < Y ∧ Y < Z ∧ Solution A B C X Y Z := by
  have h := sol.2.1
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at h
  obtain ⟨A,hA,B,hB,C,hC,ab,bc⟩ := sorted_labels (a := a) (b := b) (c := c)
    (by grind) (by grind) (by grind)
  obtain ⟨X,hX,Y,hY,Z,hZ,xy,yz⟩ := sorted_labels (a := x) (b := y) (c := z)
    (by grind) (by grind) (by grind)
  have row : [A,B,C] ⊆ [a,b,c] := by
    simp only [List.cons_subset, List.nil_subset, and_true]
    exact ⟨hA, hB, hC⟩
  have col : [X,Y,Z] ⊆ [x,y,z] := by
    simp only [List.cons_subset, List.nil_subset, and_true]
    exact ⟨hX, hY, hZ⟩
  refine ⟨A,hA,B,hB,C,hC,X,hX,Y,hY,Z,hZ,ab,bc,xy,yz,?_,?_,?_⟩
  · apply List.all_eq_true.mpr
    intro i hi
    change i ∈ [A,B,C] ++ [X,Y,Z] at hi
    apply List.all_eq_true.mp sol.1
    exact (List.mem_append.mp hi).elim
      (fun h => List.mem_append_left [x,y,z] (row h)) (fun h => List.mem_append_right [a,b,c] (col h))
  · apply (List.nodup_append (l₁ := [A,B,C]) (l₂ := [X,Y,Z])).mpr
    refine ⟨?_, ?_, ?_⟩
    · simp; omega
    · simp; omega
    · have orig := ((List.nodup_append (l₁ := [a,b,c]) (l₂ := [x,y,z])).mp sol.2.1).2.2
      exact fun i hi j hj => orig i (row hi) j (col hj)
  · exact fun i hi j hj => sol.2.2 i (row hi) j (col hj)

/-- Enumerate each side of a solution in increasing order, retaining the nine edges. -/
theorem ordered_sides {a b c x y z : Nat} (sol : Solution a b c x y z) :
    ∃ A ∈ [a,b,c], ∃ B ∈ [a,b,c], ∃ C ∈ [a,b,c],
    ∃ X ∈ [x,y,z], ∃ Y ∈ [x,y,z], ∃ Z ∈ [x,y,z],
    A < B ∧ B < C ∧ X < Y ∧ Y < Z ∧ (∀ i ∈ [A,B,C], ∀ j ∈ [X,Y,Z], Edge i j) := by
  obtain ⟨A,hA,B,hB,C,hC,X,hX,Y,hY,Z,hZ,ab,bc,xy,yz,sorted⟩ := ordered_solution_sides sol
  exact ⟨A,hA,B,hB,C,hC,X,hX,Y,hY,Z,hZ,ab,bc,xy,yz,sorted.2.2⟩

/-- If all six labels lie between m and M, their maxima must grow at least
    quartically with the lower endpoint. -/
theorem solution_quartic_gap {a b c x y z m M : Nat} (sol : Solution a b c x y z)
    (bounds : ∀ i ∈ [a,b,c,x,y,z], m ≤ i ∧ i ≤ M) : 8*m^4 < M := by
  obtain ⟨A,hA,B,hB,C,hC,X,hX,Y,hY,Z,hZ,ab,bc,xy,yz,edges⟩ := ordered_sides sol
  have rs {v : Nat} (h : v ∈ [a,b,c]) := bounds v (List.mem_append_left [x,y,z] h)
  have cs {v : Nat} (h : v ∈ [x,y,z]) := bounds v (List.mem_append_right [a,b,c] h)
  have bot := Nat.mul_le_mul (rs hA).1 (cs hX).1
  have mid := Nat.mul_le_mul (rs hB).1 (cs hY).1
  have top := Nat.mul_le_mul (rs hC).2 (cs hZ).2
  have cap := Nat.mul_le_mul (Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left bot 3))
    (show m*m ≤ B*Y+1 by omega)
  apply Nat.mul_self_lt_mul_self_iff.mp
  have norm : (8*m^4)*(8*m^4) = 64*(m*m)^3*(m*m) := by grind
  exact norm ▸ Nat.lt_of_le_of_lt cap (Nat.lt_of_lt_of_le (ordered_edges_height_gap ab bc xy yz edges) top)

end SquareTriples
