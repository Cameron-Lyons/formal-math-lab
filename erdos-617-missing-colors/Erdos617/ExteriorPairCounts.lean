import Erdos617.ExteriorBlocks
import Erdos617.CoveringIncidence

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
private theorem singleton_remainder {G : SimpleGraph V} {B : Finset V} {x y : V} :
    y∈nonneighborRemainder G B {x} ↔ y∈B ∧ ¬G.Adj x y := by simp

private theorem pair_remainder {G : SimpleGraph V} {B : Finset V} {x z y : V} :
    y∈nonneighborRemainder G B {x,z} ↔ y∈B ∧ ¬G.Adj x y ∧ ¬G.Adj z y := by simp

theorem exterior_row_blocked_pairs (G : SimpleGraph V) (A B : Finset V)
    (pos : B.Nonempty) (cap : ∀ u∈B,(A.filter fun w => G.Adj w u).card≤2)
    (free : ∀ w∈A,(nonneighborRemainder G B {w}).Nonempty) :
    (A.offDiag.filter fun p => nonneighborRemainder G B {p.1,p.2}=∅).card≤8 := by
  classical
  obtain ⟨u,ub⟩ := pos
  let H := A.filter fun x => G.Adj x u
  let K (x z : V) := nonneighborRemainder G B {x,z}=∅
  let W (x : V) : Finset V := if hx : x∈A then {(free x hx).choose} else ∅
  have atW (x : V) (hx : x∈H) : ∃ u∈B, ¬G.Adj x u ∧ W x={u} := by
    have ha := (mem_filter.mp hx).1
    obtain ⟨ub,ne⟩ := singleton_remainder.mp (free x ha).choose_spec
    exact ⟨_,ub,ne,by simp [W,ha]⟩
  have heavy (x : V) (hx : x∈A) (z : V) (hz : z∈A) (k : K x z) : x∈H ∨ z∈H := by
    by_cases hit : G.Adj x u
    · exact Or.inl (mem_filter.mpr ⟨hx,hit⟩)
    right
    apply mem_filter.mpr
    refine ⟨hz,?_⟩
    by_contra missing
    have mem : u∈nonneighborRemainder G B {x,z} := pair_remainder.mpr ⟨ub,hit,missing⟩
    exact (eq_empty_iff_forall_notMem.mp k) u mem
  have bound := covering_ordered_pairs_bound A H W G.Adj K 2 1 (by
    intro x hx u hu
    obtain ⟨v,hv,_,eq⟩ := atW x hx
    obtain rfl := mem_singleton.mp (eq ▸ hu)
    exact cap _ hv) (by
    intro x hx
    obtain ⟨u,_,_,eq⟩ := atW x hx
    simp [eq]) heavy (by
    intro x hx z hz hk
    obtain ⟨u,ub,ne,eq⟩ := atW x hx
    refine ⟨u,by simp [eq],?_⟩
    by_contra za
    have blk : nonneighborRemainder G B {x,z}=∅ := hk.elim id (fun k => by simpa [K,pair_comm] using k)
    have mem := pair_remainder.mpr ⟨ub,ne,za⟩
    simp [blk] at mem)
  have few : H.card≤2 := cap u ub
  exact bound.trans (by omega)

/-- A vertex whose remaining core is a clique hits at least r vertices
of the core. The column degree bound allows at most three such vertices. -/
theorem exterior_core_blocked_singletons (G : SimpleGraph V) (A H : Finset V) {r : ℕ}
    (hr : 0<r) (size : H.card=2*r-1)
    (clcap : ∀ S⊆H,G.IsClique (S : Set V) → S.card≤r-1)
    (cap : ∀ u∈H,(A.filter fun w => G.Adj w u).card≤2) :
    (A.filter fun x => G.IsClique (nonneighborRemainder G H {x} : Set V)).card≤3 := by
  classical
  let T := heavyIncidences A H G.Adj (2*r)
  have sub : (A.filter fun x => G.IsClique (nonneighborRemainder G H {x} : Set V))⊆T := by
    intro x hx
    obtain ⟨ax,cl⟩ := mem_filter.mp hx
    have small := clcap _ (filter_subset ..) cl
    have eq : nonneighborRemainder G H {x} = H.filter fun y => ¬G.Adj x y := by ext; simp
    change (nonneighborRemainder G H {x}).card≤r-1 at small
    rw [eq] at small
    have all := card_filter_add_card_filter_not (s:=H) (G.Adj x)
    exact mem_filter.mpr ⟨ax,by omega⟩
  have le := incidence_heavy_bound A H G.Adj (2*r) 2 cap
  change (2*r)*T.card≤2*2*H.card at le
  have few : T.card≤3 := by
    by_contra! more
    have m := Nat.mul_le_mul_left (2*r) more
    omega
  exact (card_le_card sub).trans few

/-- If singleton remainders all contain a nonedge, at most 32 ordered
pairs can leave a clique in the core. -/
theorem exterior_core_blocked_pairs (G : SimpleGraph V) (A H : Finset V) {r : ℕ}
    (hr : 0<r) (size : H.card=2*r-1)
    (clcap : ∀ S⊆H,G.IsClique (S : Set V) → S.card≤r-1)
    (cap : ∀ u∈H,(A.filter fun w => G.Adj w u).card≤2)
    (free : ∀ w∈A,¬G.IsClique (nonneighborRemainder G H {w} : Set V)) :
    (A.offDiag.filter fun p => G.IsClique (nonneighborRemainder G H {p.1,p.2} : Set V)).card≤32 := by
  classical
  have notcl : ¬G.IsClique (H : Set V) := by
    intro cl
    have le := clcap H (Subset.rfl) cl
    omega
  obtain ⟨u,v,uv,miss⟩ := G.not_isClique_iff.mp notcl
  let T := A.filter fun w => G.Adj w u.val ∨ G.Adj w v.val
  let K (x z : V) := G.IsClique (nonneighborRemainder G H {x,z} : Set V)
  have wit (x : V) (hx : x∈A) : ∃ D : Finset V,D⊆nonneighborRemainder G H {x} ∧ D.card≤2 ∧ ¬G.IsClique (D : Set V) := by
    obtain ⟨u,v,ne,miss⟩ := G.not_isClique_iff.mp (free x hx)
    have dist : u.val≠v.val := fun e => ne (Subtype.ext e)
    exact ⟨{u.val,v.val},by intro q hq; rcases mem_insert.mp hq with rfl|hq; exact u.property; exact mem_singleton.mp hq ▸ v.property,card_insert_le .. |>.trans_eq (by simp),
      fun cl => miss (cl (by simp) (by simp) dist)⟩
  let W (x : V) : Finset V := if hx : x∈A then (wit x hx).choose else ∅
  have atW (x : V) (hx : x∈T) :
      W x⊆nonneighborRemainder G H {x} ∧ (W x).card≤2 ∧ ¬G.IsClique (W x : Set V) := by
    have ha := (mem_filter.mp hx).1
    simpa [W,ha] using (wit x ha).choose_spec
  have heavy (x : V) (hx : x∈A) (z : V) (hz : z∈A) (k : K x z) : x∈T ∨ z∈T := by
    by_cases h : G.Adj x u.val ∨ G.Adj x v.val
    · exact Or.inl (mem_filter.mpr ⟨hx,h⟩)
    refine Or.inr (mem_filter.mpr ⟨hz,?_⟩)
    by_contra b
    push Not at h b
    exact miss (k (pair_remainder.mpr ⟨u.property,h.1,b.1⟩) (pair_remainder.mpr ⟨v.property,h.2,b.2⟩)
      (fun eq => uv (Subtype.ext eq)))
  have bound := covering_ordered_pairs_bound A T W G.Adj K 2 2 (by
    intro x hx u hu
    exact cap u (singleton_remainder.mp ((atW x hx).1 hu)).1) (by
    intro x hx
    exact (atW x hx).2.1) heavy (by
    intro x hx z hz hk
    have cl : G.IsClique (nonneighborRemainder G H {x,z} : Set V) := hk.elim id (fun k => by simpa [K,pair_comm] using k)
    by_contra! none
    exact (atW x hx).2.2 (cl.subset (by
      intro u hu
      obtain ⟨hH,ne⟩ := singleton_remainder.mp ((atW x hx).1 hu)
      exact pair_remainder.mpr ⟨hH,ne,none u hu⟩)))
  have union : T=(A.filter fun w => G.Adj w u.val)∪(A.filter fun w => G.Adj w v.val) := by
    ext; simp [T, and_or_left]
  have few : T.card≤4 := by
    rw [union]
    exact (card_union_le ..).trans (Nat.add_le_add (cap _ u.property) (cap _ v.property))
  exact bound.trans (by omega)

end Erdos617
