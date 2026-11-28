import E1486

/-! The forward reduction from a table to arrows. The converse construction is in
`Simple.AdditionalResults`. -/

namespace E1486.Simple

variable {S : Type}

/-- A two-step route a → i → b. Loops and repeated vertices are allowed. -/
def Walk (G : S → S → Prop) (a i b : S) := G a i ∧ G i b

/-- A marked vertex lies on a closed two-step route; these will be the squares. -/
def Marked (G : S → S → Prop) (q : S) := ∃ i, Walk G q i q

/-- The three arrow rules in the README: unique midpoints, access to every square,
and a square predecessor for every vertex. -/
structure Conditions (G : S → S → Prop) : Prop where
  unique : ∀ {a b i j}, Walk G a i b → Walk G a j b → i = j
  reach : ∀ a q, Marked G q → ∃ i, Walk G a i q
  parent : ∀ b, ∃ q, Marked G q ∧ G q b

/-- Draw both kinds of arrows: a → a⋆q for each square q, and b² → b. -/
def arrows (op : S → S → S) (a b : S) : Prop :=
  Pred (Row op) (fun b => op b b) a b

/-- Whenever b already has an incoming arrow of the first kind, the arrow b² → b
is also of the first kind. Take a square q with b = v⋆q. E1486 gives
b⋆q² = q and then b²⋆q = b. -/
private theorem incoming_square {op : S → S → S} (h : Law op) {v b : S}
    (e : Row op v b) : Row op (op b b) b := by
  obtain ⟨z, rfl⟩ := e
  exact ⟨z, recover_target h v ⟨z, rfl⟩⟩

/-- The route a → a⋆q → q reaches any square q from any vertex a. -/
private theorem walk_to_square {op : S → S → S} (h : Law op) (a : S) {q : S}
    (hq : Square op q) : Walk (arrows op) a (op a q) q := by
  obtain ⟨z, rfl⟩ := hq
  exact ⟨Or.inl ⟨z, rfl⟩, Or.inl ⟨op z z, return_to_square h a ⟨z, rfl⟩⟩⟩

theorem marked_iff_square {op : S → S → S} (h : Law op) (b : S) :
    Marked (arrows op) b ↔ Square op b := by
  constructor
  · rintro ⟨i, (hb | hi), hi'⟩
    · exact ⟨i, returnOnEdge h hi' hb⟩
    · exact ⟨i,hi⟩
  · intro hb
    exact ⟨op b b, walk_to_square h b hb⟩

theorem fromLaw {op : S → S → S} (h : Law op) : Conditions (arrows op) where
  unique {a b i j} pi pj := by
    by_cases hb : ∃ v, Row op v b
    · have last {v} (e : arrows op v b) : Row op v b :=
        e.elim id (fun he => he ▸ incoming_square h hb.choose_spec)
      exact (returnOnEdge h pi.1 (last pi.2)).symm.trans
        (returnOnEdge h pj.1 (last pj.2))
    · have only {v} (e : arrows op v b) : op b b = v :=
        e.elim (fun hr => (hb ⟨v,hr⟩).elim) id
      exact (only pi.2).symm.trans (only pj.2)
  reach a q hq := ⟨op a q, walk_to_square h a ((marked_iff_square h q).mp hq)⟩
  parent b := ⟨op b b, (marked_iff_square h _).mpr ⟨b,rfl⟩, Or.inr rfl⟩

end E1486.Simple
