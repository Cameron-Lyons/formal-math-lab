import SpliceSymmetry

/-! A global symmetry reduction for an unrestricted exact enumeration.
No list of discovered boards or cap families is used here. -/
namespace TBoards.ExactSymmetry

def allPatterns : List Pattern :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun l =>
  (List.range 3).flatMap fun m => (List.range 3).map fun r => (a,l,m,r)

theorem mem_allPatterns (p : Pattern) : p ∈ allPatterns ↔
    p.1 < 3 ∧ p.2.1 < 3 ∧ p.2.2.1 < 3 ∧ p.2.2.2 < 3 := by
  rcases p with ⟨a,l,m,r⟩
  simp only [allPatterns, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a',ha,l',hl,m',hm,r',hr,he⟩
    cases he
    exact ⟨ha,hl,hm,hr⟩
  · rintro ⟨ha,hl,hm,hr⟩
    exact ⟨a,ha,l,hl,m,hm,r,hr,rfl⟩

theorem complete_patterns {b : Board} (h : Valid b) :
    (patterns b).Perm allPatterns := by
  apply List.perm_iff_count.mpr
  intro p
  by_cases hp : p ∈ allPatterns
  · obtain ⟨ha,hl,hm,hr⟩ := (mem_allPatterns p).mp hp
    rcases p with ⟨a,l,m,r⟩
    rw [h.pattern_count a l m r ha hl hm hr]
    have count : (allPatterns.count (a,l,m,r)) = 1 := by
      have tab : ∀ a l m r : Fin 3,
          allPatterns.count (a.val,l.val,m.val,r.val) = 1 := by decide
      exact tab ⟨a,ha⟩ ⟨l,hl⟩ ⟨m,hm⟩ ⟨r,hr⟩
    exact count.symm
  · have hb : p ∉ patterns b := by
      intro hm
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hm
      exact hp ((mem_allPatterns _).mpr
        (patternAt_colors h.1 q ((mem_placements q).mp hq)))
    rw [List.count_eq_zero_of_not_mem hb, List.count_eq_zero_of_not_mem hp]

theorem pattern_injective {b : Board} (h : Valid b) {p q : Placement}
    (hp : IsPlacement p) (hq : IsPlacement q)
    (he : patternAt b p = patternAt b q) : p = q := by
  obtain ⟨ha,hl,hm,hr⟩ := patternAt_colors h.1 p hp
  obtain ⟨u,_,_,hu⟩ := h.unique_placement
    ⟨(patternAt b p).1,ha⟩ ⟨(patternAt b p).2.1,hl⟩
    ⟨(patternAt b p).2.2.1,hm⟩ ⟨(patternAt b p).2.2.2,hr⟩
  exact (hu p hp rfl).trans (hu q hq he.symm).symm

def reflectPlacement (p : Placement) : Placement := (p.1, 2*p.1-p.2)

theorem reflected_placement {p : Placement} (hp : IsPlacement p) :
    IsPlacement (reflectPlacement p) := by
  unfold IsPlacement reflectPlacement at *
  dsimp at *
  omega

theorem reflect_twice {p : Placement} (hp : IsPlacement p) :
    reflectPlacement (reflectPlacement p) = p := by
  rcases p with ⟨r,j⟩
  simp only [reflectPlacement, Prod.mk.injEq, true_and]
  unfold IsPlacement at hp
  dsimp at hp
  omega

private theorem cell_reverse {b : Board} (h : WellFormed b)
    {r j : Nat} (hr : r < 10) (hj : j < 2*r+1) :
    cell (b.map List.reverse) r j = cell b r (2*r-j) := by
  have hrow := h.2.1 r (List.mem_range.mpr hr)
  have hr' : r < b.length := h.1 ▸ hr
  have h1 : j < (b.getD r []).reverse.length := by rw [List.length_reverse, hrow]; exact hj
  have h2 : 2*r-j < (b.getD r []).length := by omega
  unfold cell
  rw [map_getD_in_bounds _ _ _ _ _ hr', ← List.getElem_eq_getD 0 (h := h1),
    ← List.getElem_eq_getD 0 (h := h2), List.getElem_reverse]
  congr 1
  omega

def reflectPattern (p : Pattern) : Pattern := (p.1,p.2.2.2,p.2.2.1,p.2.1)

theorem pattern_reverse {b : Board} (h : WellFormed b)
    {p : Placement} (hp : IsPlacement p) :
    patternAt (b.map List.reverse) p = reflectPattern (patternAt b (reflectPlacement p)) := by
  rcases p with ⟨r,j⟩
  unfold IsPlacement at hp
  dsimp at hp
  simp only [patternAt, reflectPattern, reflectPlacement]
  rw [cell_reverse h (by omega) (by omega), cell_reverse h (by omega) (by omega),
      cell_reverse h (by omega) (by omega), cell_reverse h (by omega) (by omega)]
  have e1 : 2*(r+1)-j = (2*r-j)+2 := by omega
  have e2 : 2*(r+1)-(j+1) = (2*r-j)+1 := by omega
  have e3 : 2*(r+1)-(j+2) = 2*r-j := by omega
  rw [e1,e2,e3]

def actPattern (perm : List Nat) (reflect : Bool) (p : Pattern) : Pattern :=
  recolorPattern (fun c => perm.getD c 0) (if reflect then reflectPattern p else p)

def actPlacement (reflect : Bool) (p : Placement) : Placement :=
  if reflect then reflectPlacement p else p

theorem pattern_transform {b : Board} (h : Valid b)
    (perm : List Nat) (reflect : Bool) {p : Placement} (hp : IsPlacement p) :
    patternAt (transform b perm reflect) p =
      actPattern perm reflect (patternAt b (actPlacement reflect p)) := by
  cases reflect with
  | false => exact patternAt_recolor h.1 _ p hp
  | true =>
    have eq : transform b perm true = recolor (b.map List.reverse) (fun c => perm.getD c 0) := by
      simp [transform, recolor, List.map_map, Function.comp_def]
    rw [eq, patternAt_recolor (Splice.valid_reverse h).1 _ p hp, pattern_reverse h.1 hp]
    rfl

/-- A board fixed by a symmetry bijects that symmetry's fixed placements
with its fixed ordered color patterns. -/
theorem fixed_count {b : Board} (h : Valid b) (perm : List Nat) (reflect : Bool)
    (he : transform b perm reflect = b) :
    (allPatterns.countP fun p => actPattern perm reflect p == p) =
      if reflect then 9 else 81 := by
  have equiv (p : Placement) (hp : IsPlacement p) :
      patternAt b (actPlacement reflect p) = actPattern perm reflect (patternAt b p) := by
    have hq : IsPlacement (actPlacement reflect p) := by
      cases reflect <;> simp only [actPlacement, Bool.false_eq_true, ↓reduceIte]
      · exact hp
      · exact reflected_placement hp
    have twice : actPlacement reflect (actPlacement reflect p) = p := by
      cases reflect <;> simp only [actPlacement, Bool.false_eq_true, ↓reduceIte]
      exact reflect_twice hp
    have hx := pattern_transform h perm reflect hq
    rw [he, twice] at hx
    exact hx
  have hc : (patterns b).countP (fun p => actPattern perm reflect p == p) =
      placements.countP (fun p => actPlacement reflect p == p) := by
    rw [patterns, List.countP_map]
    apply List.countP_congr
    intro p hp
    have hp' := (mem_placements p).mp hp
    have hq : IsPlacement (actPlacement reflect p) := by
      cases reflect <;> simp only [actPlacement, Bool.false_eq_true, ↓reduceIte]
      · exact hp'
      · exact reflected_placement hp'
    simp only [Function.comp_apply, beq_iff_eq]
    rw [← equiv p hp']
    exact ⟨pattern_injective h hq hp', fun e => congrArg (patternAt b) e⟩
  rw [← (complete_patterns h).countP_eq (fun p => actPattern perm reflect p == p), hc]
  cases reflect <;> decide

/-- No nonidentity color-permutation/reflection symmetry fixes a valid board. -/
theorem stabilizer_trivial {b : Board} (h : Valid b) {perm : List Nat}
    (hp : perm ∈ colorPermutations) (reflect : Bool)
    (he : transform b perm reflect = b) : perm = [0,1,2] ∧ reflect = false := by
  have hc := fixed_count h perm reflect he
  have finite : ∀ p ∈ colorPermutations, ∀ r : Bool,
      (allPatterns.countP fun q => actPattern p r q == q) = (if r then 9 else 81) →
        p = [0,1,2] ∧ r = false := by decide +kernel
  exact finite perm hp reflect hc

end TBoards.ExactSymmetry

#print axioms TBoards.ExactSymmetry.stabilizer_trivial
