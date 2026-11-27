import EvenUnitFractions.Basic

namespace EvenUnitFractions

/-- A 2-coloring of `{1, ..., 3k²}` with no monochromatic `k`-term unit-fraction sum. -/
private def Avoids (k : Nat) (c : Nat → Bool) : Prop :=
  ∀ (target : Nat) (xs : List Nat),
    1 ≤ target → target ≤ 3 * k * k → xs.length = k →
    (∀ x ∈ xs, 1 ≤ x ∧ x ≤ 3 * k * k ∧ c x = c target) →
    (xs.map reciprocal).sum ≠ reciprocal target

private theorem avoids_not {k : Nat} {c : Nat → Bool} (h : Avoids k c) :
    Avoids k (fun n => !c n) := by
  intro target xs ht1 ht2 hlen hterms
  apply h target xs ht1 ht2 hlen
  intro x hx
  obtain ⟨hx1, hx2, hcol⟩ := hterms x hx
  exact ⟨hx1, hx2, by cases h1 : c x <;> cases h2 : c target <;> simp_all⟩

private theorem rat_eq_of_mul_right {x y z : Rat} (hz : 0 < z) (h : x * z = y * z) : x = y := by
  have hne : z ≠ 0 := fun h0 => by rw [h0] at hz; exact Rat.lt_irrefl hz
  simpa [Rat.mul_assoc, Rat.mul_inv_cancel _ hne] using congrArg (· * z⁻¹) h

/-- Shorthand for `1 ≤ x ≤ 3k²`. -/
private def InRange (k x : Nat) : Prop := 1 ≤ x ∧ x ≤ 3 * k * k

private theorem inRange_of_le {k x : Nat} (hk : 1 ≤ k) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) :
    InRange k x :=
  ⟨h1, Nat.le_trans h2 (by simpa using Nat.mul_le_mul_left (3 * k) hk)⟩

private theorem inRange_mul {k a b : Nat} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (ha2 : a ≤ 3 * k) (hb2 : b ≤ k) : InRange k (a * b) :=
  ⟨Nat.mul_pos ha1 hb1, Nat.mul_le_mul ha2 hb2⟩

private theorem inRange_kmul {k a : Nat} (hk : 1 ≤ k) (ha1 : 1 ≤ a) (ha2 : a ≤ 3 * k) :
    InRange k (k * a) := by
  refine ⟨Nat.mul_pos hk ha1, ?_⟩
  calc k * a ≤ k * (3 * k) := Nat.mul_le_mul_left k ha2
    _ = 3 * k * k := by rw [← Nat.mul_assoc, Nat.mul_comm k 3]

private theorem avoids_groups {k : Nat} {c : Nat → Bool} (h : Avoids k c)
    (target : Nat) (groups : List (Nat × Nat))
    (ht : InRange k target) (hlen : (groups.map Prod.fst).sum = k)
    (hmem : ∀ p ∈ groups, 0 < p.1 → InRange k p.2 ∧ c p.2 = c target)
    (hsum : (groups.map fun (m, d) => (m : Rat) * reciprocal d).sum = reciprocal target) :
    False := by
  apply h target (expand groups) ht.1 ht.2 (by rw [length_expand, hlen])
  · intro x hx
    obtain ⟨p, hp, hpos, rfl⟩ := mem_expand hx
    obtain ⟨⟨h1, h2⟩, hc⟩ := hmem p hp hpos
    exact ⟨h1, h2, hc⟩
  · rw [sum_expand, hsum]

/-- `1/a = k/(k*a)` forces `a` and `k*a` to have opposite colors for `1 ≤ a ≤ 3k`. -/
private theorem opp {k : Nat} {c : Nat → Bool} (hk : 1 ≤ k) (h : Avoids k c)
    {a : Nat} (ha1 : 1 ≤ a) (ha2 : a ≤ 3 * k) : c (k * a) = !c a := by
  cases hka : c (k * a) <;> cases ha : c a <;> try rfl
  all_goals
    exfalso
    apply avoids_groups h a [(k, k * a)] (inRange_of_le hk ha1 ha2) (by simp)
    · intro p hp _
      simp at hp; rcases hp with rfl
      exact ⟨inRange_kmul hk ha1 ha2, by simp [hka, ha]⟩
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.add_zero]
      apply rat_eq_of_mul_right (Rat.natCast_pos.mpr ha1)
      apply rat_eq_of_mul_right (Rat.natCast_pos.mpr (Nat.mul_pos hk ha1))
      have hcast : ((k * a : Nat) : Rat) = (k : Rat) * (a : Rat) := Rat.natCast_mul k a
      grind [reciprocal]

/-- Refute a monochromatic 2-group identity `m₁/d₁ + m₂/d₂ = 1/a`. -/
private theorem contra2 {k : Nat} {c : Nat → Bool} (h : Avoids k c)
    (a m₁ d₁ m₂ d₂ : Nat)
    (ha : InRange k a) (hd₁ : InRange k d₁) (hd₂ : InRange k d₂)
    (hlen : m₁ + m₂ = k)
    (hc1 : c d₁ = c a) (hc2 : c d₂ = c a)
    (heq : a * (m₁ * d₂ + m₂ * d₁) = d₁ * d₂) : False := by
  apply avoids_groups h a [(m₁, d₁), (m₂, d₂)] ha (by simp [hlen])
  · intro p hp _
    simp at hp; rcases hp with rfl | rfl
    · exact ⟨hd₁, hc1⟩
    · exact ⟨hd₂, hc2⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.add_zero]
    have hq : ((a * (m₁ * d₂ + m₂ * d₁) : Nat) : Rat) = ((d₁ * d₂ : Nat) : Rat) :=
      congrArg Nat.cast heq
    simp only [Rat.natCast_mul, Rat.natCast_add] at hq
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr ha.1)
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr hd₁.1)
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr hd₂.1)
    grind [reciprocal]

/-- Force `c d₂ = !c a` from a 2-group identity `m₁/d₁ + m₂/d₂ = 1/a` when `c d₁ = c a`. -/
private theorem force2 {k : Nat} {c : Nat → Bool} (h : Avoids k c)
    (a m₁ d₁ m₂ d₂ : Nat)
    (ha : InRange k a) (hd₁ : InRange k d₁) (hd₂ : InRange k d₂)
    (hlen : m₁ + m₂ = k) (hc1 : c d₁ = c a)
    (heq : a * (m₁ * d₂ + m₂ * d₁) = d₁ * d₂) : c d₂ = !c a := by
  cases h2 : c d₂ <;> cases ha' : c a <;> try rfl
  all_goals
    exfalso
    exact contra2 h a m₁ d₁ m₂ d₂ ha hd₁ hd₂ hlen hc1 (by simp [h2, ha']) heq

/-- Refute a monochromatic 3-group identity `m₁/d₁ + m₂/d₂ + m₃/d₃ = 1/a`. -/
private theorem contra3 {k : Nat} {c : Nat → Bool} (h : Avoids k c)
    (a m₁ d₁ m₂ d₂ m₃ d₃ : Nat)
    (ha : InRange k a) (hd₁ : InRange k d₁) (hd₂ : InRange k d₂) (hd₃ : InRange k d₃)
    (hlen : m₁ + m₂ + m₃ = k)
    (hc1 : c d₁ = c a) (hc2 : c d₂ = c a) (hc3 : c d₃ = c a)
    (heq : a * (m₁ * d₂ * d₃ + m₂ * d₁ * d₃ + m₃ * d₁ * d₂) = d₁ * d₂ * d₃) : False := by
  apply avoids_groups h a [(m₁, d₁), (m₂, d₂), (m₃, d₃)] ha (by simp [← Nat.add_assoc, hlen])
  · intro p hp _
    simp at hp; rcases hp with rfl | rfl | rfl
    · exact ⟨hd₁, hc1⟩
    · exact ⟨hd₂, hc2⟩
    · exact ⟨hd₃, hc3⟩
  · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Rat.add_zero]
    have hq : ((a * (m₁ * d₂ * d₃ + m₂ * d₁ * d₃ + m₃ * d₁ * d₂) : Nat) : Rat) =
        ((d₁ * d₂ * d₃ : Nat) : Rat) := congrArg Nat.cast heq
    simp only [Rat.natCast_mul, Rat.natCast_add] at hq
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr ha.1)
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr hd₁.1)
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr hd₂.1)
    apply rat_eq_of_mul_right (Rat.natCast_pos.mpr hd₃.1)
    grind [reciprocal]

/-- Force `c d₃ = !c a` from a 3-group identity when `c d₁ = c d₂ = c a`. -/
private theorem force3 {k : Nat} {c : Nat → Bool} (h : Avoids k c)
    (a m₁ d₁ m₂ d₂ m₃ d₃ : Nat)
    (ha : InRange k a) (hd₁ : InRange k d₁) (hd₂ : InRange k d₂) (hd₃ : InRange k d₃)
    (hlen : m₁ + m₂ + m₃ = k) (hc1 : c d₁ = c a) (hc2 : c d₂ = c a)
    (heq : a * (m₁ * d₂ * d₃ + m₂ * d₁ * d₃ + m₃ * d₁ * d₂) = d₁ * d₂ * d₃) : c d₃ = !c a := by
  cases h3 : c d₃ <;> cases ha' : c a <;> try rfl
  all_goals
    exfalso
    exact contra3 h a m₁ d₁ m₂ d₂ m₃ d₃ ha hd₁ hd₂ hd₃ hlen hc1 hc2 (by simp [h3, ha']) heq

/-- Case 1: `c 2 ≠ c 3` is impossible for every even `k = 2s ≥ 4`. -/
private theorem case1 {s : Nat} {c : Nat → Bool} (hs : 2 ≤ s)
    (h : Avoids (2 * s) c) (h2 : c 2 = true) (h3 : c 3 = false) : False := by
  let k := 2 * s
  have h2k : c (k * 2) = false := by simpa [h2] using opp (by omega) h (a := 2) (by omega) (by omega)
  have h3k : c (k * 3) = true := by simpa [h3] using opp (by omega) h (a := 3) (by omega) (by omega)
  have h3kk : c (k * (k * 3)) = false := by
    simpa [h3k] using opp (by omega) h (a := k * 3) (by omega) (by omega)
  have r (x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) := inRange_of_le (k := k) (by omega) h1 h2
  -- 1/2 = s/(3k) + s/(3s) forces c(3s) = false
  have h3s : c (3 * s) = false := by
    simpa [h2] using force2 h 2 s (k * 3) s (3 * s)
      (r 2 (by omega) (by omega)) (r (k * 3) (by omega) (by omega)) (r (3 * s) (by omega) (by omega))
      (by omega) (by simp [h2, h3k]) (by grind)
  -- 1/3 = (s - 1)/(3s) + 1/(2k) + s/(3k²)
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  exact contra3 h 3 t (3 * (t + 1)) 1 (k * 2) (t + 1) (k * (k * 3))
    (r 3 (by omega) (by omega)) (r (3 * (t + 1)) (by omega) (by omega))
    (r (k * 2) (by omega) (by omega)) (inRange_kmul (by omega) (by omega) (by omega))
    (by omega) (by simp [h3s, h3]) (by simp [h2k, h3]) (by simp [h3kk, h3]) (by grind)

/-- Case 2: `c 1 = c 2 = c 3 = true` and `c 4 = false` is impossible for every even `k = 2s ≥ 4`. -/
private theorem case2 {s : Nat} {c : Nat → Bool} (hs : 2 ≤ s)
    (h : Avoids (2 * s) c) (h1 : c 1 = true) (h2 : c 2 = true) (h3 : c 3 = true) (h4 : c 4 = false) :
    False := by
  by_cases hs2 : s = 2
  · subst hs2
    have h6 : c 6 = false := by
      simpa [h1] using force2 h 1 2 3 2 6 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
        ⟨by omega, by omega⟩ (by omega) (by simp [h1, h3]) (by decide)
    have h16 : c 16 = true := by simpa [h4] using opp (by omega) h (a := 4) (by omega) (by omega)
    have h24 : c 24 = true := by simpa [h6] using opp (by omega) h (a := 6) (by omega) (by omega)
    exact contra3 h 2 1 3 2 16 1 24 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by simp [h2, h3]) (by simp [h2, h16]) (by simp [h2, h24]) (by decide)
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    let k := 2 * (t + 3)
    have r (x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) := inRange_of_le (k := k) (by omega) h1 h2
    have r6 : InRange k (6 * (2 * t + 4)) := inRange_mul (by omega) (by omega) (by omega) (by omega)
    -- 1 = 2/3 + (k-2)/(3(k-2)) and 1 = 1/2 + 1/3 + (k-2)/(6(k-2))
    have h3km2 : c (3 * (2 * t + 4)) = false := by
      simpa [h1] using force2 h 1 2 3 (2 * t + 4) (3 * (2 * t + 4))
        (r 1 (by omega) (by omega)) (r 3 (by omega) (by omega))
        (r (3 * (2 * t + 4)) (by omega) (by omega)) (by omega) (by simp [h1, h3]) (by grind)
    have h6km2 : c (6 * (2 * t + 4)) = false := by
      simpa [h1] using force3 h 1 1 2 1 3 (2 * t + 4) (6 * (2 * t + 4))
        (r 1 (by omega) (by omega)) (r 2 (by omega) (by omega)) (r 3 (by omega) (by omega)) r6
        (by omega) (by simp [h1, h2]) (by simp [h1, h3]) (by grind)
    -- 1/4 = (s-3)/(3(k-2)) + (s+3)/(6(k-2))
    exact contra2 h 4 t (3 * (2 * t + 4)) (t + 6) (6 * (2 * t + 4))
      (r 4 (by omega) (by omega)) (r (3 * (2 * t + 4)) (by omega) (by omega)) r6
      (by omega) (by simp [h3km2, h4]) (by simp [h6km2, h4]) (by grind)

/-- One step of Gaiser–Ramezanpour's dyadic ladder `(2q, 3q, 4q) → (6q, 8q)` for `4q ≤ k`. -/
private theorem ladder_step {t : Nat} {c : Nat → Bool}
    (h : Avoids (2 * (t + 3)) c) (col : Bool) (q : Nat) (hq : 1 ≤ q) (h4q : 4 * q ≤ 2 * (t + 3))
    (hc2 : c (2 * q) = col) (hc3 : c (3 * q) = col) (hc4 : c (4 * q) = col) :
    c (6 * q) = col ∧ c (8 * q) = col := by
  let k := 2 * (t + 3)
  have r (x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) := inRange_of_le (k := k) (by omega) h1 h2
  have r61 : InRange k (6 * q * (2 * t + 5)) := inRange_mul (by omega) (by omega) (by omega) (by omega)
  have r121 : InRange k (12 * q * (2 * t + 5)) := inRange_mul (by omega) (by omega) (by omega) (by omega)
  have r62 : InRange k (6 * q * (2 * t + 4)) := inRange_mul (by omega) (by omega) (by omega) (by omega)
  have r122 : InRange k (12 * q * (2 * t + 4)) := inRange_mul (by omega) (by omega) (by omega) (by omega)
  have hb1 : c (6 * q * (2 * t + 5)) = !col := by
    simpa [hc2] using force2 h (2 * q) 1 (3 * q) (2 * t + 5) (6 * q * (2 * t + 5))
      (r (2 * q) (by omega) (by omega)) (r (3 * q) (by omega) (by omega)) r61
      (by omega) (by simp [hc2, hc3]) (by grind)
  have hb2 : c (12 * q * (2 * t + 5)) = !col := by
    simpa [hc3] using force2 h (3 * q) 1 (4 * q) (2 * t + 5) (12 * q * (2 * t + 5))
      (r (3 * q) (by omega) (by omega)) (r (4 * q) (by omega) (by omega)) r121
      (by omega) (by simp [hc3, hc4]) (by grind)
  have h6q : c (6 * q) = col := by
    cases h6b : c (6 * q) <;> cases col <;> try rfl
    all_goals
      exfalso
      exact contra2 h (6 * q) (2 * t + 4) (6 * q * (2 * t + 5)) 2 (12 * q * (2 * t + 5))
        (r (6 * q) (by omega) (by omega)) r61 r121
        (by omega) (by simp [hb1, h6b]) (by simp [hb2, h6b]) (by grind)
  have hb3 : c (6 * q * (2 * t + 4)) = !col := by
    simpa [hc2] using force2 h (2 * q) 2 (6 * q) (2 * t + 4) (6 * q * (2 * t + 4))
      (r (2 * q) (by omega) (by omega)) (r (6 * q) (by omega) (by omega)) r62
      (by omega) (by simp [hc2, h6q]) (by grind)
  have hb4 : c (12 * q * (2 * t + 4)) = !col := by
    simpa [hc2] using force3 h (2 * q) 1 (4 * q) 1 (6 * q) (2 * t + 4) (12 * q * (2 * t + 4))
      (r (2 * q) (by omega) (by omega)) (r (4 * q) (by omega) (by omega))
      (r (6 * q) (by omega) (by omega)) r122
      (by omega) (by simp [hc2, hc4]) (by simp [hc2, h6q]) (by grind)
  have h8q : c (8 * q) = col := by
    cases h8b : c (8 * q) <;> cases col <;> try rfl
    all_goals
      exfalso
      exact contra2 h (8 * q) t (6 * q * (2 * t + 4)) (t + 6) (12 * q * (2 * t + 4))
        (r (8 * q) (by omega) (by omega)) r62 r122
        (by omega) (by simp [hb3, h8b]) (by simp [hb4, h8b]) (by grind)
  exact ⟨h6q, h8q⟩

private theorem ladder {t : Nat} {c : Nat → Bool}
    (h : Avoids (2 * (t + 3)) c) (col : Bool)
    (h2 : c 2 = col) (h3 : c 3 = col) (h4 : c 4 = col) :
    ∀ m : Nat, 1 ≤ m → 2 * 2 ^ m ≤ 2 * (t + 3) →
      c (2 * 2 ^ m) = col ∧ c (3 * 2 ^ m) = col ∧ c (4 * 2 ^ m) = col := by
  intro m hm hbound
  induction m with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero =>
      have hstep := ladder_step h col 1 (by omega) (by simpa using hbound)
        (by simpa using h2) (by simpa using h3) (by simpa using h4)
      exact ⟨by simpa using h4, by simpa using hstep.1, by simpa using hstep.2⟩
    | succ u =>
      have hpow : 2 ^ (u + 2) = 2 * 2 ^ (u + 1) := by rw [Nat.pow_succ]; omega
      obtain ⟨hp2, hp3, hp4⟩ := ih (by omega) (by omega)
      have hstep := ladder_step h col (2 ^ (u + 1)) (Nat.one_le_pow _ _ (by omega))
        (by omega) hp2 hp3 hp4
      refine ⟨?_, ?_, ?_⟩
      · have h1 : 2 * 2 ^ (u + 2) = 4 * 2 ^ (u + 1) := by omega
        rw [h1]; exact hp4
      · have h1 : 3 * 2 ^ (u + 2) = 6 * 2 ^ (u + 1) := by omega
        rw [h1]; exact hstep.1
      · have h1 : 4 * 2 ^ (u + 2) = 8 * 2 ^ (u + 1) := by omega
        rw [h1]; exact hstep.2

private theorem exists_dyadic_bracket (k : Nat) (hk : 4 ≤ k) :
    ∃ m : Nat, 1 ≤ m ∧ 2 * 2 ^ m ≤ k ∧ k < 4 * 2 ^ m := by
  induction k using Nat.strongRecOn with
  | ind n ih =>
    by_cases h8 : n < 8
    · exact ⟨1, by omega, by omega, by omega⟩
    · obtain ⟨m, hm, hlo, hhi⟩ := ih (n / 2) (by omega) (by omega)
      have h1 : 2 * 2 ^ (m + 1) = 4 * 2 ^ m := by rw [Nat.pow_succ]; omega
      have h2 : 4 * 2 ^ (m + 1) = 8 * 2 ^ m := by rw [Nat.pow_succ]; omega
      exact ⟨m + 1, by omega, by omega, by omega⟩

/-- Case 3: `c 1 = c 2 = c 3 = c 4 = true` is impossible for every even `k = 2s ≥ 4`. -/
private theorem case3 {s : Nat} {c : Nat → Bool} (hs : 2 ≤ s)
    (h : Avoids (2 * s) c) (h1 : c 1 = true) (h2 : c 2 = true) (h3 : c 3 = true) (h4 : c 4 = true) :
    False := by
  by_cases hs2 : s = 2
  · subst hs2
    have := opp (by omega) h (a := 1) (by omega) (by omega)
    simp [h1, h4] at this
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    let k := 2 * (t + 3)
    obtain ⟨m, hm, hlo, hhi⟩ := exists_dyadic_bracket k (by omega)
    obtain ⟨hc2p, _, hc4p⟩ := ladder h true h2 h3 h4 m hm hlo
    let p := 2 ^ m
    have hp : 2 ≤ p := by simpa [p] using Nat.pow_le_pow_right (by omega : 0 < 2) hm
    obtain ⟨u, hu⟩ : ∃ u, 4 * p = k + u := ⟨4 * p - k, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, k = 2 * p + v := ⟨k - 2 * p, by omega⟩
    have r (x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) := inRange_of_le (k := k) (by omega) h1 h2
    -- 1 = (4p - k)/(2p) + 2(k - 2p)/(4p)
    exact contra2 h 1 u (2 * p) (2 * v) (4 * p)
      (r 1 (by omega) (by omega)) (r (2 * p) (by omega) (by omega)) (r (4 * p) (by omega) (by omega))
      (by omega) (by simp [p, hc2p, h1]) (by simp [p, hc4p, h1]) (by grind)

/-- Case 4: `c 1 = true` and `c 2 = c 3 = false` is impossible for every even `k = 2s ≥ 4`. -/
private theorem case4 {s : Nat} {c : Nat → Bool} (hs : 2 ≤ s)
    (h : Avoids (2 * s) c) (h1 : c 1 = true) (h2 : c 2 = false) (h3 : c 3 = false) : False := by
  let k := 2 * s
  have hk_col : c k = false := by simpa [h1] using opp (by omega) h (a := 1) (by omega) (by omega)
  have h2k : c (k * 2) = true := by simpa [h2] using opp (by omega) h (a := 2) (by omega) (by omega)
  have h3k : c (k * 3) = true := by simpa [h3] using opp (by omega) h (a := 3) (by omega) (by omega)
  have h2kk : c (k * (k * 2)) = false := by
    simpa [h2k] using opp (by omega) h (a := k * 2) (by omega) (by omega)
  have h3kk : c (k * (k * 3)) = false := by
    simpa [h3k] using opp (by omega) h (a := k * 3) (by omega) (by omega)
  have r (x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ 3 * k) := inRange_of_le (k := k) (by omega) h1 h2
  -- 1/k = 1/(3s) + 2/(2k²) + (k-3)/(3k²) forces c(3s) = true
  have h3s : c (3 * s) = true := by
    obtain ⟨w, hw⟩ : ∃ w, k = w + 3 := ⟨k - 3, by omega⟩
    simpa [hk_col] using force3 h k 2 (k * (k * 2)) w (k * (k * 3)) 1 (3 * s)
      (r k (by omega) (by omega))
      (inRange_kmul (by omega) (by omega) (by omega))
      (inRange_kmul (by omega) (by omega) (by omega))
      (r (3 * s) (by omega) (by omega))
      (by omega) (by simp [h2kk, hk_col]) (by simp [h3kk, hk_col]) (by grind)
  by_cases hs2 : s = 2
  · subst hs2
    -- k = 4: c 4 = c k = false, c 6 = c(3s) = true => c 24 = false, and 1/3 = 1/4 + 1/24 + 2/48
    have h24 : c 24 = false := by simpa [h3s] using opp (by omega) h (a := 6) (by omega) (by omega)
    exact contra3 h 3 1 4 1 24 2 48 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      (by simpa [k, h3] using hk_col) (by simp [h24, h3]) (by simpa [k, h3] using h3kk) (by decide)
  · obtain ⟨t, rfl⟩ : ∃ t, s = t + 3 := ⟨s - 3, by omega⟩
    -- Force c 4 = false in one line: 1 = 3/4 + 3/12 (k = 6) or 1 = 2/4 + 6/(3s) + (k-8)/(2k) (k ≥ 8)
    have h4 : c 4 = false := by
      cases h4' : c 4
      · rfl
      · exfalso
        cases t with
        | zero =>
          exact contra2 h 1 3 4 3 12 ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
            ⟨by omega, by omega⟩ (by omega) (by simp [h1, h4']) (by simpa [k, h1] using h2k)
            (by decide)
        | succ u =>
          exact contra3 h 1 2 4 6 (3 * (u + 4)) (2 * u) (k * 2)
            (r 1 (by omega) (by omega)) (r 4 (by omega) (by omega))
            (r (3 * (u + 4)) (by omega) (by omega)) (r (k * 2) (by omega) (by omega))
            (by omega) (by simp [h1, h4']) (by simp [h1, h3s]) (by simp [h1, h2k]) (by grind)
    -- Dyadic ladder gives 2p, 3p, 4p all false, hence 3pk and 4pk true
    obtain ⟨m, hm, hlo, hhi⟩ := exists_dyadic_bracket k (by omega)
    obtain ⟨hc2p, hc3p, hc4p⟩ := ladder h false h2 h3 h4 m hm hlo
    let p := 2 ^ m
    have hp : 2 ≤ p := by simpa [p] using Nat.pow_le_pow_right (by omega : 0 < 2) hm
    have h3pk : c (k * (3 * p)) = true := by
      simpa [p, hc3p] using opp (by omega) h (a := 3 * p) (by omega) (by omega)
    have h4pk : c (k * (4 * p)) = true := by
      simpa [p, hc4p] using opp (by omega) h (a := 4 * p) (by omega) (by omega)
    by_cases hle : 3 * k ≤ 8 * p
    · -- 1/(3s) = (8p - 3k)/(3pk) + (4k - 8p)/(4pk)
      obtain ⟨a, ha⟩ : ∃ a, 8 * p = 3 * k + a := ⟨8 * p - 3 * k, by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, 4 * k = 8 * p + b := ⟨4 * k - 8 * p, by omega⟩
      exact contra2 h (3 * (t + 3)) a (k * (3 * p)) b (k * (4 * p))
        (r (3 * (t + 3)) (by omega) (by omega))
        (inRange_kmul (by omega) (by omega) (by omega))
        (inRange_kmul (by omega) (by omega) (by omega))
        (by omega) (by simp [h3pk, h3s]) (by simp [h4pk, h3s]) (by grind)
    · -- Force 4p(k-1) and 6p(k-1) true, then 1/(3s) = (2p-s)/(3pk) + (4p-k-2)/(4p(k-1)) + (5s-6p+2)/(6p(k-1))
      have r4p1 : InRange k (4 * p * (2 * t + 5)) :=
        inRange_mul (by omega) (by omega) (by omega) (by omega)
      have r6p1 : InRange k (6 * p * (2 * t + 5)) :=
        inRange_mul (by omega) (by omega) (by omega) (by omega)
      have h4p1 : c (4 * p * (2 * t + 5)) = true := by
        simpa [p, hc2p] using force2 h (2 * p) 1 (4 * p) (2 * t + 5) (4 * p * (2 * t + 5))
          (r (2 * p) (by omega) (by omega)) (r (4 * p) (by omega) (by omega)) r4p1
          (by omega) (by simp [p, hc2p, hc4p]) (by grind)
      have h6p1 : c (6 * p * (2 * t + 5)) = true := by
        simpa [p, hc2p] using force2 h (2 * p) 1 (3 * p) (2 * t + 5) (6 * p * (2 * t + 5))
          (r (2 * p) (by omega) (by omega)) (r (3 * p) (by omega) (by omega)) r6p1
          (by omega) (by simp [p, hc2p, hc3p]) (by grind)
      obtain ⟨a, ha⟩ : ∃ a, 2 * p = (t + 3) + a := ⟨2 * p - (t + 3), by omega⟩
      obtain ⟨b, hb⟩ : ∃ b, 4 * p = k + 2 + b := ⟨4 * p - k - 2, by omega⟩
      obtain ⟨c0, hc0⟩ : ∃ c0, 5 * (t + 3) + 2 = 6 * p + c0 := ⟨5 * (t + 3) + 2 - 6 * p, by omega⟩
      exact contra3 h (3 * (t + 3))
        a (k * (3 * p)) b (4 * p * (2 * t + 5)) c0 (6 * p * (2 * t + 5))
        (r (3 * (t + 3)) (by omega) (by omega))
        (inRange_kmul (by omega) (by omega) (by omega)) r4p1 r6p1
        (by omega) (by simp [h3pk, h3s]) (by simp [h4p1, h3s]) (by simp [h6p1, h3s]) (by grind)

/-- Main upper bound: for every even integer `k ≥ 4`, `f₂(k) ≤ 3k²`. -/
theorem upper {k : Nat} (heven : k % 2 = 0) (hk : 4 ≤ k) : Forces k (3 * k * k) := by
  obtain ⟨s, rfl⟩ : ∃ s, k = 2 * s := ⟨k / 2, by omega⟩
  have hs : 2 ≤ s := by omega
  intro color
  exact Classical.byContradiction fun hno => by
    have havoid : Avoids (2 * s) color := by
      intro target xs ht1 ht2 hlen hterms hsum
      exact hno ⟨target, xs, ht1, ht2, hlen, hterms, hsum⟩
    cases h1 : color 1 <;> cases h2 : color 2 <;> cases h3 : color 3
    · have hnot := avoids_not havoid
      cases h4 : color 4
      · exact case3 hs hnot (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
      · exact case2 hs hnot (by simp [h1]) (by simp [h2]) (by simp [h3]) (by simp [h4])
    · exact case1 hs (avoids_not havoid) (by simp [h2]) (by simp [h3])
    · exact case1 hs havoid h2 h3
    · exact case4 hs (avoids_not havoid) (by simp [h1]) (by simp [h2]) (by simp [h3])
    · exact case4 hs havoid h1 h2 h3
    · exact case1 hs (avoids_not havoid) (by simp [h2]) (by simp [h3])
    · exact case1 hs havoid h2 h3
    · cases h4 : color 4
      · exact case2 hs havoid h1 h2 h3 h4
      · exact case3 hs havoid h1 h2 h3 h4

end EvenUnitFractions
