import PolynomialGeometry
import PolynomialCRTTable

/-! An arbitrary polynomial parametrization modulo 75 contributes at most 50
distinct points in general position. Fixing the input modulo 5 leaves output
coordinates with constant low base-5 digits. Remove those digits and divide
by 5. In this 15 by 15 grid the output pairs lie on one affine line modulo 5,
because 5² vanishes modulo 25, and occupy at most three pairs modulo 3.
The separately checked table covers each such support by five ordinary lines.
Each of the five input classes therefore contributes at most ten points. -/
namespace Grid75.ModularCurve.CRT

open Grid75.CRT (Line lineResidue tripleResidue locate combine)

private def reduce (k : Nat) [NeZero k] (a : Z75) : Fin k := Fin.ofNat k a.val
private def coefficients (k : Nat) [NeZero k] (p : List Z75) := p.map (reduce k)

private theorem arith25 : ∀ a b : Z75,
    reduce 25 (a+b) = reduce 25 a + reduce 25 b ∧ reduce 25 (a*b) = reduce 25 a * reduce 25 b := by
  set_option maxRecDepth 10000 in decide +kernel
private theorem arith3 : ∀ a b : Z75,
    reduce 3 (a+b) = reduce 3 a + reduce 3 b ∧ reduce 3 (a*b) = reduce 3 a * reduce 3 b := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem commute (k : Nat) [NeZero k] (h : ∀ a b : Z75,
    reduce k (a+b) = reduce k a + reduce k b ∧ reduce k (a*b) = reduce k a * reduce k b)
    (p : List Z75) (x : Z75) : reduce k (evaluate p x) = Polynomial.evalAt (coefficients k p) (reduce k x) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [evaluate, coefficients, List.map_cons, Polynomial.evalAt, (h _ _).1, (h _ _).2]
    exact congrArg (fun z => reduce k a + reduce k x * z) ih

def input (r : Fin 5) (j : Fin 15) : Z75 := ⟨r.val+5*j.val, by omega⟩
private def r25 (r : Fin 5) : Fin 25 := ⟨r.val, by omega⟩
private def j25 (j : Fin 15) : Fin 25 := ⟨j.val, by omega⟩
private def j5 (j : Fin 15) : Fin 5 := Fin.ofNat 5 j.val
private theorem input25 : ∀ r j, reduce 25 (input r j)=r25 r + 5*j25 j := by decide +kernel

private def xyLow (p : List Z75) (r : Fin 5) : Fin 5 := Fin.ofNat 5 (Polynomial.evalAt (coefficients 25 p) (r25 r)).val
private def base5 (p : List Z75) (r : Fin 5) : Fin 5 := Fin.ofNat 5 ((Polynomial.evalAt (coefficients 25 p) (r25 r)).val/5)
private def slope5 (p : List Z75) (r : Fin 5) : Fin 5 := Fin.ofNat 5 (Polynomial.slopeAt (coefficients 25 p) (r25 r)).val
private def compressed (p : List Z75) (t : Z75) : Fin 15 :=
  ⟨(evaluate p t).val / 5, by have e := (evaluate p t).isLt; omega⟩

private theorem raw_digits : ∀ (a d : Fin 25) (j : Fin 15),
    (a + 5*j25 j*d).val % 5 = a.val % 5 ∧
    (a + 5*j25 j*d).val / 5 = ((Fin.ofNat 5 (a.val/5)) + (Fin.ofNat 5 d.val) * j5 j).val := by
  set_option maxRecDepth 10000 in decide +kernel

private theorem base_digits : ∀ x : Z75,
  x.val % 5 = (reduce 25 x).val % 5 ∧ (x.val/5)%5 = (reduce 25 x).val / 5 := by decide +kernel

theorem mod5_profile (p : List Z75) (r : Fin 5) (j : Fin 15) :
    (evaluate p (input r j)).val % 5 = (xyLow p r).val ∧
    (compressed p (input r j)).val % 5 = (base5 p r + slope5 p r * j5 j).val := by
  have h := base_digits (evaluate p (input r j))
  rw [commute 25 arith25, input25, Polynomial.first_order _ _ 5 _ (by decide)] at h
  have g := raw_digits (Polynomial.evalAt (coefficients 25 p) (r25 r)) (Polynomial.slopeAt (coefficients 25 p) (r25 r)) j
  exact ⟨h.1.trans g.1, h.2.trans g.2⟩

private def base3 (p : List Z75) (r : Fin 5) (a : Fin 3) : Fin 3 :=
  2 * (Polynomial.evalAt (coefficients 3 p) a - Fin.ofNat 3 (xyLow p r).val)

private theorem digit3 : ∀ x : Z75, (x.val/5)%3 =
    (2 * (reduce 3 x - Fin.ofNat 3 (x.val % 5))).val := by decide +kernel

theorem mod3_profile (p : List Z75) (r : Fin 5) (j : Fin 15) :
    (compressed p (input r j)).val % 3 = (base3 p r (reduce 3 (input r j))).val := by
  have h := digit3 (evaluate p (input r j))
  rw [commute 3 arith3, (mod5_profile p r j).1] at h
  exact h

-- The F5 and F3 components determining the fifteen candidate cells.
private def lineThrough (a b u v : Fin 5) : Fin 30 :=
  if u = 0 then ⟨25+a.val, by omega⟩ else
    let slope := v*u^3
    let intercept := b - slope*a
    ⟨5*slope.val + intercept.val, by have := slope.isLt; have := intercept.isLt; omega⟩

private theorem choose_line (a b u v : Fin 5) : ∃ l : Fin 30,
    ∀ j : Fin 5, ∃ i : Fin 5, lineResidue l.val i.val = ((a+u*j).val,(b+v*j).val) := by
  refine ⟨lineThrough a b u v, fun j => ⟨if u = 0 then b+v*j else a+u*j, ?_⟩⟩
  revert a b u v j
  set_option maxRecDepth 2000 in decide +kernel

private def inMask (m : Fin 84) (a : Fin 9) : Bool :=
  (List.finRange 3).any fun k => tripleResidue m.val k.val == a.val

private theorem choose_mask (a b c : Fin 9) : ∃ m : Fin 84,
    (∃ k : Fin 3, tripleResidue m.val k.val = a.val) ∧
    (∃ k : Fin 3, tripleResidue m.val k.val = b.val) ∧
    (∃ k : Fin 3, tripleResidue m.val k.val = c.val) := by
  have h : (List.finRange 9).all (fun a => (List.finRange 9).all (fun b =>
      (List.finRange 9).all (fun c => (List.finRange 84).any fun m =>
        inMask m a && inMask m b && inMask m c))) = true := by
    set_option maxHeartbeats 0 in decide +kernel
  have cover := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h a
    (List.mem_finRange _)) b (List.mem_finRange _)) c (List.mem_finRange _)
  obtain ⟨m, _, hm⟩ := List.any_eq_true.mp cover
  have mem (r : Fin 9) (hr : inMask m r) : ∃ k : Fin 3, tripleResidue m.val k.val = r.val := by
    obtain ⟨k, _, hk⟩ := List.any_eq_true.mp hr
    exact ⟨k, beq_iff_eq.mp hk⟩
  obtain ⟨hab, hc⟩ := Bool.and_eq_true_iff.mp hm
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hab
  exact ⟨m, mem a ha, mem b hb, mem c hc⟩

private def mod3pair (p q : List Z75) (r : Fin 5) (z : Fin 3) : Fin 9 :=
  ⟨(base3 p r z).val + 3*(base3 q r z).val, by have a := (base3 p r z).isLt; have b := (base3 q r z).isLt; omega⟩

private theorem choose_mask_for (p q : List Z75) (r : Fin 5) : ∃ m : Fin 84,
    ∀ z : Fin 3, ∃ k : Fin 3, tripleResidue m.val k.val = (mod3pair p q r z).val := by
  let g := mod3pair p q r
  obtain ⟨m,h0,h1,h2⟩ := choose_mask (g 0) (g 1) (g 2)
  refine ⟨m, ?_⟩
  intro z
  have h : z = 0 ∨ z = 1 ∨ z = 2 := by revert z; decide
  rcases h with h | h | h <;> subst z <;> assumption

def index15 (j : Fin 5) (k : Fin 3) : Fin 15 := ⟨j.val+5*k.val,by omega⟩

private theorem combine_residues : ∀ x : Fin 15, combine (x.val % 5) (x.val % 3) = x.val := by decide

private theorem profile (p q : List Z75) (r : Fin 5) :
    ∃ l : Fin 30, ∃ m : Fin 84, ∀ j : Fin 15, ∃ g : Fin 15,
    Grid75.CRT.locate l.val m.val g.val =
      ((compressed p (input r j)).val, (compressed q (input r j)).val) := by
  obtain ⟨l,hl⟩ := choose_line (base5 p r) (base5 q r) (slope5 p r) (slope5 q r)
  obtain ⟨m,hm⟩ := choose_mask_for p q r
  refine ⟨l,m,?_⟩
  intro j
  obtain ⟨i,hi⟩ := hl (j5 j)
  obtain ⟨k,hk⟩ := hm (reduce 3 (input r j))
  refine ⟨index15 i k, ?_⟩
  let x := compressed p (input r j)
  let y := compressed q (input r j)
  have h5 : lineResidue l.val i.val = (x.val % 5, y.val % 5) := by
    rw [hi, (mod5_profile p r j).2, (mod5_profile q r j).2]
  have h3 : tripleResidue m.val k.val = x.val % 3 + 3 * (y.val % 3) := by
    rw [hk, mod3_profile p r j, mod3_profile q r j]
    rfl
  have mod5 : (index15 i k).val % 5 = i.val := by dsimp [index15]; omega
  have div5 : (index15 i k).val / 5 = k.val := by dsimp [index15]; omega
  simp only [locate, mod5, div5, h5, h3]
  have mod3 : (x.val % 3 + 3 * (y.val % 3)) % 3 = x.val % 3 := by omega
  have div3 : (x.val % 3 + 3 * (y.val % 3)) / 3 = y.val % 3 := by omega
  rw [mod3, div3, combine_residues, combine_residues]

private def selected (L : Line) (p : Point) : Bool := L.contains p.1.val p.2.val

private theorem collinear (L : Line) (a b c : Point)
    (ha : selected L a) (hb : selected L b) (hc : selected L c) : det a b c = 0 := by
  have ⟨hne, aH⟩ := of_decide_eq_true ha
  have bH := (of_decide_eq_true hb).2
  have cH := (of_decide_eq_true hc).2
  rcases hne with h | h
  · have eq : det a b c * L.dx = 0 := by unfold det; grind
    exact (Int.mul_eq_zero.mp eq).resolve_right h
  · have eq : det a b c * L.dy = 0 := by unfold det; grind
    exact (Int.mul_eq_zero.mp eq).resolve_right h

private theorem cover_25_lines {s : List Point} (hs : NoThree s) (lines : Fin 5 → Fin 5 → Line) :
    ∃ cover : List Point, cover.length ≤ 50 ∧
      ∀ p ∈ s, ∀ r i, selected (lines r i) p → p ∈ cover := by
  let pts (r i : Fin 5) := s.filter (selected (lines r i))
  let many (r : Fin 5) := (List.finRange 5).flatMap (pts r)
  have count {α : Type} (f : α → List Point) (B : Nat) (hb : ∀ i,(f i).length ≤ B)
      (l : List α) : (l.flatMap f).length ≤ B * l.length := by
    induction l with
    | nil => simp
    | cons a t ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
      have := hb a; omega
  have per (r) : (many r).length ≤ 10 := by
    simpa [many] using count (pts r) 2 (fun i => hs.line_bound _ (collinear (lines r i))) (List.finRange 5)
  refine ⟨(List.finRange 5).flatMap many, ?_, ?_⟩
  · simpa using count many 10 per (List.finRange 5)
  · intro p hp r i h
    exact List.mem_flatMap.mpr ⟨r, List.mem_finRange _, List.mem_flatMap.mpr
      ⟨i, List.mem_finRange _, List.mem_filter.mpr ⟨hp, h⟩⟩⟩

/-- Lift a line in a residue square back to the original grid. -/
private def liftLine (lowX lowY : Nat) (s : Line) : Line :=
  {s with x := (lowX : Int) + 5*s.x, y := (lowY : Int) + 5*s.y}

private theorem lift_hit (s : Line) (lowX lowY x y : Nat) (h : s.contains x y) :
    (liftLine lowX lowY s).contains (lowX + 5*x : Nat) (lowY + 5*y : Nat) := by
  obtain ⟨hne, eq⟩ := of_decide_eq_true h
  apply decide_eq_true
  refine ⟨hne, ?_⟩
  simp only [liftLine, Int.natCast_add, Int.natCast_mul]
  grind

private theorem decomposed (t : Z75) : ∃ r j, t = input r j := by revert t; decide +kernel

/-- Fifty points suffice to cover the selected part of any polynomial image. -/
theorem small_cover_50 (p q : List Z75) {s : List Point} (hs : NoThree s) :
    ∃ cover : List Point, cover.length ≤ 50 ∧ ∀ t, point p q t ∈ s → point p q t ∈ cover := by
  classical
  let l (r) := Classical.choose (profile p q r)
  let m (r) := Classical.choose (Classical.choose_spec (profile p q r))
  let word r := Grid75.CRT.selectWord (l r) (m r)
  let lines (r : Fin 5) (i : Fin 5) := liftLine (xyLow p r).val (xyLow q r).val
    (Grid75.CRT.segmentAt (word r) i)
  obtain ⟨cover, size, mem⟩ := cover_25_lines hs lines
  refine ⟨cover, size, ?_⟩
  intro t ht
  obtain ⟨r, j, rfl⟩ := decomposed t
  obtain ⟨g,loc⟩ := Classical.choose_spec (Classical.choose_spec (profile p q r)) j
  let i := Grid75.CRT.segmentIndex (word r) g.val
  apply mem _ ht r i
  have h := Grid75.CRT.selected_certifies (l r) (m r) g
  change (Grid75.CRT.segmentAt (word r) i).contains
    (locate (l r).val (m r).val g.val).1 (locate (l r).val (m r).val g.val).2 = true at h
  rw [loc] at h
  have liftCoord (f : List Z75) : (evaluate f (input r j)).val =
      (xyLow f r).val + 5*(compressed f (input r j)).val := by
    have eq := (mod5_profile f r j).1
    dsimp [compressed]
    omega
  change (lines r i).contains (evaluate p (input r j)).val (evaluate q (input r j)).val = true
  rw [liftCoord p, liftCoord q]
  exact lift_hit _ _ _ _ _ h

/-- One polynomial image contains at most fifty selected points. -/
theorem one_curve_bound_50 (p q : List Z75) {s : List Point} (nd : s.Nodup) (hs : NoThree s)
    (hc : ∀ z ∈ s, ∃ t, z = point p q t) : s.length ≤ 50 := by
  obtain ⟨cover, bound, mem⟩ := small_cover_50 p q hs
  apply Nat.le_trans (nd.length_le_of_subset (l₂ := cover) ?_) bound
  intro z hz
  obtain ⟨t, rfl⟩ := hc z hz
  exact mem t hz

/-- Two polynomial images contain at most one hundred selected points. -/
theorem two_curves_bound_100 (p q u v : List Z75) {s : List Point} (nd : s.Nodup) (hs : NoThree s)
    (hc : ∀ z ∈ s, (∃ t, z = point p q t) ∨ (∃ t, z = point u v t)) : s.length ≤ 100 := by
  obtain ⟨a, la, ma⟩ := small_cover_50 p q hs
  obtain ⟨b, lb, mb⟩ := small_cover_50 u v hs
  have sub : s ⊆ a ++ b := by
    intro z hz
    rcases hc z hz with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · exact List.mem_append_left _ (ma t hz)
    · exact List.mem_append_right _ (mb t hz)
  have h := nd.length_le_of_subset sub
  rw [List.length_append] at h
  omega

end Grid75.ModularCurve.CRT

namespace Grid75.ModularCurve

/-- A cover padded to exactly sixty entries. -/
theorem small_cover (p q : List Z75) {s : List Point} (hs : NoThree s) :
    ∃ cover : List Point, cover.length = 60 ∧
      ∀ t : Z75, point p q t ∈ s → point p q t ∈ cover := by
  classical
  obtain ⟨c, bound, mem⟩ := CRT.small_cover_50 p q hs
  let image := c.filter fun z => decide (∃ t, z = point p q t)
  have count : image.length ≤ c.length := List.length_filter_le ..
  refine ⟨image ++ List.replicate (60 - image.length) (point p q 0), ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    omega
  · intro t ht
    exact List.mem_append_left _ (List.mem_filter.mpr ⟨mem t ht, decide_eq_true ⟨t, rfl⟩⟩)

theorem one_curve_bound (p q : List Z75) {s : List Point} (nd : s.Nodup) (hs : NoThree s)
    (contained : ∀ z ∈ s, ∃ t, z = point p q t) : s.length ≤ 60 :=
  Nat.le_trans (CRT.one_curve_bound_50 p q nd hs contained) (by decide)

theorem two_curves_bound (p q u v : List Z75) {s : List Point} (nd : s.Nodup) (hs : NoThree s)
    (contained : ∀ z ∈ s, (∃ t, z = point p q t) ∨ (∃ t, z = point u v t)) : s.length ≤ 120 :=
  Nat.le_trans (CRT.two_curves_bound_100 p q u v nd hs contained) (by decide)

end Grid75.ModularCurve
