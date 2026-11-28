import BoardData

namespace TBoards

/-- Apply an arbitrary color map to every cell. -/
def recolor (b : Board) (f : Nat → Nat) : Board := b.map (List.map f)

def recolorPattern (f : Nat → Nat) (p : Pattern) : Pattern :=
  (f p.1, f p.2.1, f p.2.2.1, f p.2.2.2)

theorem map_getD_in_bounds {α β : Type} (xs : List α) (f : α → β)
    (i : Nat) (d : α) (e : β) (hi : i < xs.length) :
    (xs.map f).getD i e = f (xs.getD i d) := by
  rw [← List.getElem_eq_getD e (h := by simpa using hi),
    ← List.getElem_eq_getD d (h := hi)]
  simp

theorem WellFormed.recolor {b : Board} (h : WellFormed b)
    (f : Nat → Nat) (hf : ∀ c, c < 3 → f c < 3) : WellFormed (TBoards.recolor b f) := by
  refine ⟨by simpa [TBoards.recolor] using h.1, ?_, ?_⟩
  · intro r hr
    have hrb : r < b.length := by have := List.mem_range.mp hr; have := h.1; omega
    rw [TBoards.recolor, map_getD_in_bounds b (List.map f) r [] [] hrb, List.length_map]
    exact h.2.1 r hr
  · intro row hrow c hc
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨oldc, holdc, rfl⟩ := List.mem_map.mp hc
    exact hf oldc (h.2.2 old hold oldc holdc)

theorem cell_recolor {b : Board} (h : WellFormed b) (f : Nat → Nat)
    (r j : Nat) (hr : r < 10) (hj : j < 2*r+1) :
    cell (TBoards.recolor b f) r j = f (cell b r j) := by
  have hrb : r < b.length := by have := h.1; omega
  have hlen := h.2.1 r (List.mem_range.mpr hr)
  unfold cell TBoards.recolor
  rw [map_getD_in_bounds b (List.map f) r [] [] hrb]
  exact map_getD_in_bounds (b.getD r []) f j 0 0 (by omega)

theorem patternAt_recolor {b : Board} (h : WellFormed b) (f : Nat → Nat)
    (p : Placement) (hp : IsPlacement p) :
    patternAt (TBoards.recolor b f) p = recolorPattern f (patternAt b p) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := placement_bounds hp
  simp only [patternAt, recolorPattern]
  rw [cell_recolor h f _ _ h0 h1, cell_recolor h f _ _ h2 h3,
      cell_recolor h f _ _ h2 h4, cell_recolor h f _ _ h2 h5]

theorem patternAt_colors {b : Board} (h : WellFormed b)
    (p : Placement) (hp : IsPlacement p) :
    (patternAt b p).1 < 3 ∧ (patternAt b p).2.1 < 3 ∧
    (patternAt b p).2.2.1 < 3 ∧ (patternAt b p).2.2.2 < 3 := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := placement_bounds hp
  have getColor (r j : Nat) (hr : r < 10) (hj : j < 2*r+1) : cell b r j < 3 := by
    obtain ⟨_,_,_,_,hc⟩ := h.cell_is_entry r j hr hj
    exact hc
  exact ⟨getColor _ _ h0 h1, getColor _ _ h2 h3,
    getColor _ _ h2 h4, getColor _ _ h2 h5⟩

theorem recolor_eq_iff (f g : Nat → Nat)
    (hgf : ∀ c, c < 3 → g (f c) = c)
    (hfg : ∀ c, c < 3 → f (g c) = c)
    (c d : Nat) (hc : c < 3) (hd : d < 3) : f c = d ↔ c = g d := by
  constructor
  · intro he
    have := congrArg g he
    rw [hgf c hc] at this
    exact this
  · intro he
    rw [he, hfg d hd]

/-- Color bijections preserve all ordered-pattern multiplicities. -/
theorem Valid.recolor {b : Board} (h : Valid b) (f g : Nat → Nat)
    (hf : ∀ c, c < 3 → f c < 3) (hg : ∀ c, c < 3 → g c < 3)
    (hgf : ∀ c, c < 3 → g (f c) = c)
    (hfg : ∀ c, c < 3 → f (g c) = c) : Valid (TBoards.recolor b f) := by
  refine ⟨h.1.recolor f hf, ?_⟩
  intro a l m r
  have hc : (patterns (TBoards.recolor b f)).count (a.val,l.val,m.val,r.val) =
      (patterns b).count (g a.val,g l.val,g m.val,g r.val) := by
    simp only [patterns, List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro p hp
    have hp' := (mem_placements p).mp hp
    have hcs := patternAt_colors h.1 p hp'
    simp only [Function.comp_apply, beq_iff_eq]
    rw [patternAt_recolor h.1 f p hp']
    simp only [recolorPattern, Prod.ext_iff]
    exact and_congr (recolor_eq_iff f g hgf hfg _ _ hcs.1 a.isLt)
      (and_congr (recolor_eq_iff f g hgf hfg _ _ hcs.2.1 l.isLt)
        (and_congr (recolor_eq_iff f g hgf hfg _ _ hcs.2.2.1 m.isLt)
          (recolor_eq_iff f g hgf hfg _ _ hcs.2.2.2 r.isLt)))
  rw [hc]
  exact h.2 ⟨g a.val,hg _ a.isLt⟩ ⟨g l.val,hg _ l.isLt⟩
    ⟨g m.val,hg _ m.isLt⟩ ⟨g r.val,hg _ r.isLt⟩

def PaletteInverse (p q : List Nat) : Prop :=
  (∀ c : Fin 3, p.getD c.val 0 < 3) ∧
  (∀ c : Fin 3, q.getD c.val 0 < 3) ∧
  (∀ c : Fin 3, q.getD (p.getD c.val 0) 0 = c.val) ∧
  (∀ c : Fin 3, p.getD (q.getD c.val 0) 0 = c.val)

instance (p q : List Nat) : Decidable (PaletteInverse p q) := by
  unfold PaletteInverse
  infer_instance

theorem colorPermutations_have_inverse :
    ∀ p ∈ colorPermutations, ∃ q ∈ colorPermutations, PaletteInverse p q := by decide

/-- Any of the six global palette renamings preserves validity. -/
theorem valid_transform_colors {b : Board} (h : Valid b)
    (p : List Nat) (hp : p ∈ colorPermutations) : Valid (transform b p false) := by
  obtain ⟨q, _, hf, hg, hgf, hfg⟩ := colorPermutations_have_inverse p hp
  change Valid (TBoards.recolor b (fun c => p.getD c 0))
  exact h.recolor (fun c => p.getD c 0) (fun c => q.getD c 0)
    (fun c hc => hf ⟨c,hc⟩) (fun c hc => hg ⟨c,hc⟩)
    (fun c hc => hgf ⟨c,hc⟩) (fun c hc => hfg ⟨c,hc⟩)

/-- Certifying a board and its horizontal reflection suffices for its full orbit.
This avoids rechecking any of the six global palette renamings. -/
theorem orbit_valid_of_valid_and_reverse {b : Board}
    (h : Valid b) (hr : Valid (b.map List.reverse)) : ∀ c ∈ orbit b, Valid c := by
  intro c hc
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact valid_transform_colors h p hp
  · simpa [transform, List.map_map, Function.comp_def] using valid_transform_colors hr p hp

end TBoards
#print axioms TBoards.valid_transform_colors

#print axioms TBoards.orbit_valid_of_valid_and_reverse
