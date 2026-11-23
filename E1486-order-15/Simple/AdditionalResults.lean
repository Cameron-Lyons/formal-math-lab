import Simple.Graph
import Normalize
import SymmetryCore

/-! Related results that are not needed by `E1486.Simple.noTable`.

This module preserves the graph reconstruction theorems, extra square-row facts,
and the older maximization of square-row graphs. Import it to use these results;
the order-15 proof does not depend on it.
-/

namespace E1486

variable {S : Type}

/- Reconstruct a table from square rows and a specified diagonal. -/

/-- Conditions on square rows and the diagonal that suffice to reconstruct a table. -/
structure Graph {S : Type} (R : S → S → Prop) (d : S → S) : Prop where
  unique : ∀ {a b i j}, Pred R d a i → R i b → Pred R d a j → R j b → i = j
  covers : ∀ a z, ∃ i, R a i ∧ R i (d z)
  diagonal : ∀ {a i}, Pred R d a i → R i a → i = d a

theorem graphOfLaw {op : S → S → S} (h : Law op) :
    Graph (Row op) (fun x => op x x) where
  unique hai hib haj hjb := (returnOnEdge h hai hib).symm.trans (returnOnEdge h haj hjb)
  covers a z := ⟨op a (op z z), ⟨z, rfl⟩, ⟨op z z, h (op z z) a z⟩⟩
  diagonal hai hia := (returnOnEdge h hai hia).symm

/-- At a cell (a,b), take the middle vertex if one exists, or the square of b. -/
noncomputable def fromGraph (R : S → S → Prop) (d : S → S) (a b : S) : S := by
  classical
  exact if h : ∃ i, Pred R d a i ∧ R i b then h.choose else d b

theorem fromGraph_path {R : S → S → Prop} {d : S → S} (g : Graph R d)
    {a i b : S} (hai : Pred R d a i) (hib : R i b) : fromGraph R d a b = i := by
  classical
  have h : ∃ j, Pred R d a j ∧ R j b := ⟨i, hai, hib⟩
  simp only [fromGraph, dite_eq_left h]
  exact g.unique h.choose_spec.1 h.choose_spec.2 hai hib

theorem fromGraph_diagonal {R : S → S → Prop} {d : S → S} (g : Graph R d) (a : S) :
    fromGraph R d a a = d a := by
  classical
  by_cases h : ∃ i, Pred R d a i ∧ R i a
  · exact (fromGraph_path g h.choose_spec.1 h.choose_spec.2).trans
      (g.diagonal h.choose_spec.1 h.choose_spec.2)
  · simp [fromGraph, h]

theorem fromGraph_column (R : S → S → Prop) (d : S → S) (a b : S) :
    Pred R d (fromGraph R d a b) b := by
  classical
  by_cases h : ∃ i, Pred R d a i ∧ R i b
  · exact Or.inl (by simpa [fromGraph, h] using h.choose_spec.2)
  · exact Or.inr (by simp [fromGraph, h])

theorem lawOfGraph {R : S → S → Prop} {d : S → S} (g : Graph R d) :
    Law (fromGraph R d) := by
  intro x y z
  rw [fromGraph_diagonal g]
  obtain ⟨i, hxi, hiz⟩ := g.covers x z
  rw [fromGraph_path g (Or.inl hxi) hiz]
  exact fromGraph_path g (fromGraph_column R d y x) hxi

theorem exists_law_iff_graph :
    (∃ op : S → S → S, Law op) ↔ ∃ (R : S → S → Prop) (d : S → S), Graph R d := by
  constructor
  · rintro ⟨op,h⟩
    exact ⟨_, _, graphOfLaw h⟩
  · rintro ⟨R,d,g⟩
    exact ⟨_, lawOfGraph g⟩

/- Further facts about squares and constant square rows. -/

theorem edge_to_square_of_incoming {op : S → S → S} (h : Law op) {x y : S}
    (hxy : Row op x y) : ∃ q, Square op q ∧ Row op y q := by
  obtain ⟨z, rfl⟩ := hxy
  exact ⟨op z z, ⟨z, rfl⟩, ⟨op z z, h (op z z) x z⟩⟩

theorem diagonal_edge_of_square_neighbor {op : S → S → S} (h : Law op) {x q : S}
    (hxq : Row op x q) (hq : Square op q) : Row op (op x x) x := by
  obtain ⟨z, hz⟩ := hxq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht, ← hz]; exact h x x z⟩

theorem square_of_mutual {op : S → S → S} (h : Law op) {x y : S}
    (hxy : Row op x y) (hyx : Row op y x) : Square op x :=
  ⟨y, returnOnEdge h (Or.inl hyx) hxy⟩

theorem square_of_hit_diagonal {op : S → S → S} (h : Law op) {x : S}
    (hx : Row op x (op x x)) : Square op x := by
  have hd := diagonal_edge_of_square_neighbor h hx ⟨x, rfl⟩
  exact square_of_mutual h hx hd

theorem distinct_fixed_no_edge {op : S → S → S} (h : Law op) {x y : S}
    (hxx : op x x = x) (hyy : op y y = y) (hxy : Row op x y) : x = y := by
  have h1 : Row op x x := ⟨x, by rw [hxx, hxx]⟩
  have h2 : Row op y y := ⟨y, by rw [hyy, hyy]⟩
  exact (graphOfLaw h).unique (Or.inl h1) hxy (Or.inl hxy) h2

/-- The project singleton-row argument, reproduced here without a Mathlib dependency.
See Spectrum/Equation1486/SingletonRow.lean at the research revision linked in README.md. -/
theorem trivial_of_constant {op : S → S → S} (h : Law op) (a b : S)
    (hc : ∀ z, op a (op z z) = b) (x y : S) : x = y := by
  have h₁ (u v : S) : op b (op (op u u) (op v v)) = op u u := by
    simpa only [hc] using h (op u u) a v
  have h₂ (u v : S) : op (op u b) (op v v) = b := by
    simpa only [h₁] using h b u (op v v)
  have h₃ (u : S) : op b (op u u) = b := by
    calc
      _ = op (op a (op (op b b) (op b b))) (op u u) := by rw [hc]
      _ = op (op a b) (op u u) := by rw [h₂ b b]
      _ = b := h₂ a u
  have h₄ (u : S) : op u u = b := (h₁ u u).symm.trans (h₃ _)
  have hba : b = a := by
    have ht := h a a a
    rw [hc, h₄, h₄] at ht
    exact ht
  have hs (u : S) : op u u = a := (h₄ u).trans hba
  have hr (u v : S) : op (op u v) (op v a) = v := by
    simpa only [hs] using h v u a
  have he (u : S) : op u a = a := by
    have ht : op (op u a) a = a := by simpa only [hs] using hr u a
    simpa only [hs, ht] using (hr (op u a) (op u a)).symm
  have hall (u : S) : u = a := by simpa only [he] using (hr a u).symm
  exact (hall x).trans (hall y).symm

theorem other_neighbor {op : Fin 15 → Fin 15 → Fin 15} (h : Law op) (x b : Fin 15) :
    ∃ c, Row op x c ∧ c ≠ b := by
  classical
  apply Classical.byContradiction
  intro hn
  have hc (z : Fin 15) : op x (op z z) = b := by
    apply Classical.byContradiction
    intro hne
    exact hn ⟨_, ⟨z, rfl⟩, hne⟩
  exact (by decide : (0 : Fin 15) ≠ 1) (trivial_of_constant h x b hc 0 1)

namespace Simple

/- Reconstruct a table directly from the arrow conditions. -/

/-- Take the midpoint if one exists, otherwise take a marked predecessor. -/
noncomputable def product {G : S → S → Prop} (h : Conditions G) (a b : S) : S := by
  classical
  exact if e : ∃ i, Walk G a i b then e.choose else (h.parent b).choose

private theorem midpoint {G : S → S → Prop} (h : Conditions G) {a i b : S} (p : Walk G a i b) :
    product h a b = i := by
  classical
  have e : ∃ i, Walk G a i b := ⟨i,p⟩
  simp only [product, dite_eq_left e]
  exact h.unique e.choose_spec p

theorem toLaw {G : S → S → Prop} (h : Conditions G) : Law (product h) := by
  classical
  have incoming (a b : S) : G (product h a b) b := by
    by_cases e : ∃ i, Walk G a i b
    · simpa [product,e] using e.choose_spec.2
    · simpa [product,e] using (h.parent b).choose_spec.2
  have marked (z : S) : Marked G (product h z z) := by
    by_cases e : ∃ i, Walk G z i z
    · rw [midpoint h e.choose_spec]
      exact ⟨z,e.choose_spec.2,e.choose_spec.1⟩
    · simpa [product,e] using (h.parent z).choose_spec.1
  intro x y z
  obtain ⟨i,hi⟩ := h.reach x _ (marked z)
  rw [midpoint h hi]
  exact midpoint h ⟨incoming y x,hi.1⟩

theorem characterization :
    (∃ op : S → S → S, Law op) ↔ ∃ G : S → S → Prop, Conditions G := by
  constructor
  · rintro ⟨op,h⟩; exact ⟨_,fromLaw h⟩
  · rintro ⟨G,h⟩; exact ⟨_,toLaw h⟩

end Simple

namespace Symmetry
open Encoding

/- Maximize the older square-row graph. The main proof instead orders the full
arrow graph in `Simple.Order`. -/

noncomputable def bits (m : Operation) (x y : V) : Bool := by
  classical exact decide (Row m x y)

theorem bits_pull (l : Label) (m : Operation) (x y : V) :
    bits (l.pull m) x y = bits m (l.old x) (l.old y) := by
  classical
  simp only [bits]
  rw [propext (l.row m x y)]

private theorem score_length (k : Nat) (r s : V → V → Bool) :
    (score k r).length = (score k s).length := by
  simp [score,matrix,profile,List.length_flatMap]

theorem maximize {m : Operation} {k j : Nat} (hn : DiagNormal m k j) (h : Law m) :
    ∃ m' : Operation, Law m' ∧ DiagNormal m' k j ∧
      ∀ m'' : Operation, Law m'' → DiagNormal m'' k j →
        score k (bits m'') ≤ score k (bits m') := by
  obtain ⟨m',⟨h',hn'⟩,hm⟩ := exists_max_key
    (fun v : Operation => Law v ∧ DiagNormal v k j)
    (fun v => score k (bits v)) _ (fun v => score_length k (bits v) (bits m)) ⟨m,h,hn⟩
  exact ⟨m',h',hn',fun v hv hn'' => hm v ⟨hv,hn''⟩⟩

end Symmetry

end E1486
