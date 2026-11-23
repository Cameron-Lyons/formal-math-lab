import Order17BoundaryObstruction
import Order17Reflection

namespace Erdos835.Order17BoundaryObstruction

open Finset TwentyPoint Order17Partial20

/-- Decode a subset mask on the labelled twenty-point ground set. -/
def blockOfMask (m : Nat) : Finset Vertex := univ.filter (fun x : Vertex => m.testBit x.val)

/-- The 145 quadruples in the partial certificate as subsets of the ground set. -/
def boundaryBlocks : List (Finset Vertex) := seed.map (fun b => blockOfMask (mask b))

private def hitsBoundary (q : Finset Vertex) : Prop :=
  ∃ b ∈ boundaryBlocks, q ≠ b ∧ 3 ≤ (q ∩ b).card

private instance (q : Finset Vertex) : Decidable (hitsBoundary q) := by
  unfold hitsBoundary
  infer_instance

private def possible (r : Requirement) := candidates.filter (meets r)

private def accounted (r : Requirement) (q : Finset Vertex) : Prop :=
  (∃ m ∈ possible r, blockOfMask m = q) ∨ hitsBoundary q

private instance (r : Requirement) (q : Finset Vertex) : Decidable (accounted r q) := by
  unfold accounted
  infer_instance

private def validShape : Requirement → Prop
  | .triple t =>
    let q := blockOfMask t
    q.card = 3 ∧ (∀ x : Vertex, x ∉ q → accounted (.triple t) (insert x q)) ∧
    (∀ b ∈ possible (.triple t), q ⊆ blockOfMask b)
  | .orbit o =>
    let q := blockOfMask o
    q.card = 4 ∧ (∀ j, accounted (.orbit o) (translate j q)) ∧
    (∀ b ∈ possible (.orbit o), ∃ j, blockOfMask b = translate j q)

private instance (r : Requirement) : Decidable (validShape r) := by
  cases r <;> unfold validShape <;> infer_instance

private theorem shapeTable : ∀ r ∈ requirements, validShape r := by native_decide

private def encode (s : Finset Vertex) : Nat := s.sum (fun x => 1 <<< x.val)

private theorem decodes : ∀ b ∈ candidates, encode (blockOfMask b) = b := by native_decide

/-- A 20-point cyclic seed cannot contain all 145 specified boundary blocks. -/
theorem no_seed_contains_boundary {D : Finset Vertex → Prop}
    (hD : QuadrupleSeed univ translate D) (included : ∀ q ∈ boundaryBlocks, D q) : False := by
  classical
  have free {q} (hq : D q) : ¬ hitsBoundary q := by
    rintro ⟨b, hb, hne, hsize⟩
    obtain ⟨t, ht, hcard⟩ := exists_subset_card_eq hsize
    have sub := subset_inter_iff.mp ht
    exact hne ((hD.triples t (subset_univ _) hcard).unique ⟨hq, sub.1⟩ ⟨included b hb, sub.2⟩)
  have rep {r q} (hq : D q) (h : accounted r q) :
      ∃ m ∈ possible r, blockOfMask m = q := h.resolve_right (free hq)
  have inj {r a b} (ha : a ∈ possible r) (hb : b ∈ possible r) (e : blockOfMask a = blockOfMask b) :
      a = b := (decodes a (List.mem_filter.mp ha).1).symm.trans
        ((congrArg encode e).trans (decodes b (List.mem_filter.mp hb).1))
  apply cannot_complete (fun b => decide (D (blockOfMask b)))
  intro r hr
  have shape := shapeTable r hr
  suffices ∃! b, b ∈ possible r ∧ D (blockOfMask b) by
    simpa only [possible, List.mem_filter, decide_eq_true_eq, and_assoc] using this
  cases r with
  | triple t =>
    obtain ⟨ht, completion, contains⟩ := shape
    obtain ⟨q, ⟨hq, hsub⟩, unique⟩ := hD.triples (blockOfMask t) (subset_univ _) ht
    obtain ⟨x, hx, heq⟩ := exists_eq_insert_iff.mpr ⟨hsub, by rw [(hD.blocks q hq).2, ht]⟩
    obtain ⟨b, hb, eb⟩ := rep hq (heq ▸ completion x hx)
    refine ⟨b, ⟨hb, eb ▸ hq⟩, ?_⟩
    rintro c ⟨hc, hDc⟩
    exact inj hc hb ((unique _ ⟨hDc, contains c hc⟩).trans eb.symm)
  | orbit o =>
    obtain ⟨ho, completion, represented⟩ := shape
    obtain ⟨j, hj, unique⟩ := hD.orbits (blockOfMask o) (subset_univ _) ho
    obtain ⟨b, hb, eb⟩ := rep hj (completion j)
    refine ⟨b, ⟨hb, eb ▸ hj⟩, ?_⟩
    rintro c ⟨hc, hDc⟩
    obtain ⟨k, ek⟩ := represented c hc
    have chosenK : D (translate k (blockOfMask o)) := by simpa only [← ek] using hDc
    have eq := unique k chosenK
    subst k
    exact inj hc hb (ek.trans eb.symm)

end Erdos835.Order17BoundaryObstruction
