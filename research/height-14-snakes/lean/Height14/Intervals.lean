import Std

/-! Along a snake, the connected pieces of a scanned prefix are intervals
of path indices. Adding a square joins the intervals of its old neighbors. -/

namespace Height14.Interval

variable {l : Nat}
abbrev Index (l : Nat) := Fin l

def nextTo (i j : Index l) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val
def between (i z j : Index l) : Prop :=
  (i.val ≤ z.val ∧ z.val ≤ j.val) ∨ (j.val ≤ z.val ∧ z.val ≤ i.val)
def joined (pos : Index l → Nat) (t : Nat) (i j : Index l) : Prop :=
  ∀ z, between i z j → pos z < t

theorem joined_refl {pos : Index l → Nat} {t} {i : Index l} :
    joined pos t i i ↔ pos i < t := by
  constructor
  · intro h
    exact h i (Or.inl ⟨Nat.le_refl _, Nat.le_refl _⟩)
  · intro h z hz
    have : z = i := Fin.ext (by unfold between at hz; omega)
    simpa [this] using h

theorem joined_symm {pos : Index l → Nat} {t} {i j : Index l}
    (h : joined pos t i j) : joined pos t j i := by
  intro z hz
  exact h z (by unfold between at *; omega)

theorem joined_trans {pos : Index l → Nat} {t} {i j k : Index l}
    (h : joined pos t i j) (g : joined pos t j k) : joined pos t i k := by
  intro z hz
  by_cases a : between i z j
  · exact h z a
  · exact g z (by unfold between at *; omega)

theorem joined_left {pos : Index l → Nat} {t} {i j : Index l}
    (h : joined pos t i j) : pos i < t :=
  h i (by unfold between; omega)

theorem joined_right {pos : Index l → Nat} {t} {i j : Index l}
    (h : joined pos t i j) : pos j < t :=
  joined_left (joined_symm h)

theorem joined_mono {pos : Index l → Nat} {t} {i j : Index l}
    (h : joined pos t i j) : joined pos (t+1) i j :=
  fun z hz => Nat.lt_succ_of_lt (h z hz)

theorem adjacent_joined {pos : Index l → Nat} {t} {i j : Index l}
    (hi : pos i < t) (hj : pos j < t) (h : nextTo i j) : joined pos t i j := by
  intro z hz
  have : z.val = i.val ∨ z.val = j.val := by unfold nextTo between at *; omega
  rcases this with e | e
  · simpa [Fin.ext e] using hi
  · simpa [Fin.ext e] using hj

def touches (pos : Index l → Nat) (t : Nat) (p i : Index l) : Prop :=
  ∃ k, nextTo k p ∧ joined pos t i k

private theorem old_of_ne {pos : Index l → Nat} (inj : ∀ ⦃i j⦄, pos i = pos j → i = j)
    {t} {p i : Index l} (hp : pos p = t) (hne : i ≠ p) (h : pos i < t+1) :
    pos i < t := by
  have : pos i ≠ pos p := fun e => hne (inj e)
  omega

private theorem endpoint_touches {pos : Index l → Nat} (inj : ∀ ⦃i j⦄, pos i = pos j → i = j)
    {t} {p i j : Index l} (hp : pos p = t) (h : joined pos (t+1) i j)
    (mid : between i p j) : i = p ∨ touches pos t p i := by
  by_cases heq : i = p
  · exact Or.inl heq
  right
  have hneq : i.val ≠ p.val := fun e => heq (Fin.ext e)
  by_cases side : i.val < p.val
  · let k : Index l := ⟨p.val-1, by have := p.isLt; omega⟩
    refine ⟨k, Or.inl (by dsimp [k]; omega), ?_⟩
    intro z hz
    have hz' : between i z j := by unfold between at *; dsimp [k] at hz; omega
    have ne : z ≠ p := by
      intro e; subst z; unfold between at hz; dsimp [k] at hz; omega
    exact old_of_ne inj hp ne (h z hz')
  · let k : Index l := ⟨p.val+1, by have := i.isLt; omega⟩
    refine ⟨k, Or.inr rfl, ?_⟩
    intro z hz
    have hz' : between i z j := by unfold between at *; dsimp [k] at hz; omega
    have ne : z ≠ p := by
      intro e; subst z; unfold between at hz; dsimp [k] at hz; omega
    exact old_of_ne inj hp ne (h z hz')

private theorem attach {pos : Index l → Nat} {t} {p i : Index l} (hp : pos p = t)
    (h : i = p ∨ touches pos t p i) : joined pos (t+1) i p := by
  rcases h with rfl | ⟨k, hk, hik⟩
  · exact joined_refl.mpr (by omega)
  · exact joined_trans (joined_mono hik)
      (adjacent_joined (Nat.lt_succ_of_lt (joined_right hik)) (by omega) hk)

theorem joined_fill {pos : Index l → Nat} (inj : ∀ ⦃i j⦄, pos i = pos j → i = j)
    {t} {p i j : Index l} (hp : pos p = t) :
    joined pos (t+1) i j ↔ joined pos t i j ∨
      ((i = p ∨ touches pos t p i) ∧ (j = p ∨ touches pos t p j)) := by
  constructor
  · intro h
    by_cases mid : between i p j
    · exact Or.inr ⟨endpoint_touches inj hp h mid,
        endpoint_touches inj hp (joined_symm h) (by unfold between at *; omega)⟩
    · left
      intro z hz
      exact old_of_ne inj hp (fun e => mid (e ▸ hz)) (h z hz)
  · rintro (h | ⟨hi, hj⟩)
    · exact joined_mono h
    · exact joined_trans (attach hp hi) (joined_symm (attach hp hj))

theorem joined_skip {pos : Index l → Nat} {t} {i j : Index l} (h : ∀ i, pos i ≠ t) :
    joined pos (t+1) i j ↔ joined pos t i j := by
  constructor
  · intro hj z hz
    have := hj z hz
    have := h z
    omega
  · exact joined_mono

/-- A path interval cannot disappear behind the scanning boundary while some
other square of the same snake remains ahead. -/
theorem exit_edge {pos : Index l → Nat} {t} (i j : Index l) (hi : pos i < t)
    (hj : t ≤ pos j) : ∃ a b, joined pos t i a ∧ nextTo a b ∧ t ≤ pos b := by
  let distance (a b : Index l) := (a.val-b.val)+(b.val-a.val)
  generalize hd : distance i j = d
  induction d using Nat.strongRecOn generalizing i with
  | ind d ih =>
    have ine : i ≠ j := by rintro rfl; omega
    have ine' : i.val ≠ j.val := fun e => ine (Fin.ext e)
    have step : ∃ k : Index l, nextTo i k ∧ distance k j < d := by
      by_cases side : i.val < j.val
      · refine ⟨⟨i.val + 1, by have := j.isLt; omega⟩, Or.inl rfl, ?_⟩
        dsimp [distance] at *; omega
      · refine ⟨⟨i.val - 1, by have := i.isLt; omega⟩, Or.inr (by dsimp; omega), ?_⟩
        dsimp [distance] at *; omega
    obtain ⟨k, adj, closer⟩ := step
    by_cases hk : pos k < t
    · obtain ⟨a,b,hka,hab,hb⟩ := ih _ closer k hk rfl
      exact ⟨a,b,joined_trans (adjacent_joined hi hk adj) hka,hab,hb⟩
    · exact ⟨i,k,joined_refl.mpr hi,adj,Nat.le_of_not_lt hk⟩

end Height14.Interval
