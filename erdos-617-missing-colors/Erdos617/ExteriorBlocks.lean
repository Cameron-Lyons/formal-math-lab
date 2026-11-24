import Erdos617.ClusterExtension
import Erdos617.OddPrivateRows
import Erdos617.RankBasic

namespace Erdos617

open Finset SimpleGraph
open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- The vertices in B that can accompany all of W in an independent set. -/
noncomputable def nonneighborRemainder (G : SimpleGraph V) (B W : Finset V) : Finset V :=
  B.filter fun v => ∀ w∈W, ¬G.Adj w v

omit [DecidableEq V] in
@[simp] theorem mem_nonneighborRemainder (G : SimpleGraph V) {B W : Finset V} {v : V} :
    v∈nonneighborRemainder G B W ↔ v∈B ∧ ∀ w∈W, ¬G.Adj w v := mem_filter

/-- If a pair of exterior vertices can use a representative from every row
and a nonedge from the last block, they extend to an independent (r+1)-set. -/
theorem exterior_pair_blocked [Fintype V] {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hr : 3≤r) (hb : Balanced c) (H : Finset V) (P : Fin (r-3) → Finset V)
    (dis : Pairwise fun i j => Disjoint (P i) (P j)) (apart : ∀ i,Disjoint (P i) H)
    (sep : ∀ i j,i≠j → ∀ u∈P i,∀ v∈P j,¬(colorGraph c k).Adj u v)
    (sepH : ∀ i,∀ u∈P i,∀ v∈H,¬(colorGraph c k).Adj u v)
    (x y : V) (xy : x≠y) (ne : ¬(colorGraph c k).Adj x y)
    (offH : Disjoint {x,y} H) (off : ∀ i,Disjoint {x,y} (P i)) :
    (∃ i,nonneighborRemainder (colorGraph c k) (P i) {x,y}=∅) ∨
      (colorGraph c k).IsClique (nonneighborRemainder (colorGraph c k) H {x,y} : Set V) := by
  classical
  let G := colorGraph c k
  by_contra! h
  obtain ⟨rows,core⟩ := h
  choose w hw using rows
  have row (i) := (mem_nonneighborRemainder G).mp (hw i)
  let I := univ.image w
  have inj : Function.Injective w := by
    intro i j eq
    by_contra ij
    exact disjoint_left.mp (dis ij) (row i).1 (eq ▸ (row j).1)
  have ind : G.IsIndepSet (I : Set V) := by
    intro a ha b hb ab
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact sep i j (fun h => ab (congrArg w h)) _ (row i).1 _ (row j).1
  obtain ⟨a,b,ab,missing⟩ := (G.not_isClique_iff).mp core
  have aH := (mem_nonneighborRemainder G).mp a.property
  have bH := (mem_nonneighborRemainder G).mp b.property
  have avoid (z : V) (hz : z∈H) : ∀ v∈I, ¬G.Adj z v := by
    intro v hv e
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact sepH i _ (row i).1 z hz e.symm
  have outsideH (z : V) (hz : z∈H) : z∉I := by
    intro h
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact disjoint_left.mp (apart i) (row i).1 hz
  let J := insert a.val (insert b.val I)
  have indepJ : G.IsIndepSet (J : Set V) := by
    apply independent_insert_of_nonadjacent _ (independent_insert_of_nonadjacent G ind b.val (avoid _ bH.1))
    intro v hv
    rcases mem_insert.mp hv with rfl|hi
    · exact missing
    · exact avoid _ aH.1 v hi
  have abv : a.val≠b.val := fun eq => ab (Subtype.ext eq)
  have sizes : J.card=(r-3)+2 := by
    simp [J,card_insert_of_notMem,abv,outsideH _ aH.1,outsideH _ bH.1,I,card_image_of_injective _ inj]
  let X : Finset V := {x,y}
  have none (z : V) (hz : z∈X) (v : V) (hv : v∈J) : ¬G.Adj z v := by
    rcases mem_insert.mp hv with rfl|h
    · exact aH.2 z hz
    rcases mem_insert.mp h with rfl|h
    · exact bH.2 z hz
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact (row i).2 z hz
  have outside (z : V) (hz : z∈X) : z∉J := by
    intro hzJ
    rcases mem_insert.mp hzJ with rfl|h
    · exact disjoint_left.mp offH hz aH.1
    rcases mem_insert.mp h with rfl|h
    · exact disjoint_left.mp offH hz bH.1
    obtain ⟨i,_,rfl⟩ := mem_image.mp h
    exact disjoint_left.mp (off i) hz (row i).1
  have hx : x∈X := mem_insert_self ..
  have hy : y∈X := by simp [X]
  have extI := independent_insert_of_nonadjacent _ (independent_insert_of_nonadjacent G indepJ y (none _ hy)) x
    (fun v hv => (mem_insert.mp hv).elim (fun eq => eq ▸ ne) (none _ hx v))
  have order : (insert x (insert y J)).card=r+1 := by
    rw [card_insert_of_notMem (by simp [xy,outside _ hx]),card_insert_of_notMem (outside _ hy),sizes]
    omega
  obtain ⟨a,ha,b,hb',ne,e⟩ := hb _ order k
  exact extI ha hb' ne ⟨ne,e⟩

/-- Two exterior lines together can pay for at most r−|B| vertices complete
to a nonempty row B. For short rows the two-spoke bound suffices. -/
theorem complete_on_two_lines {r : ℕ} {c : Sym2 V → Fin r} {k : Fin r}
    (hr : 8≤r) (hb : Balanced c) (B C D : Finset V) (pos : B.Nonempty)
    (size : B.card≤r) (cl : (colorGraph c k).IsClique (B : Set V)) (dis : Disjoint B (C∪D))
    (capC : ∀ u∈B,(C.filter fun w => (colorGraph c k).Adj w u).card≤2)
    (capD : ∀ u∈B,(D.filter fun w => (colorGraph c k).Adj w u).card≤2) :
    ((C∪D).filter fun w => ∀ u∈B,(colorGraph c k).Adj w u).card≤r-B.card := by
  classical
  let W := (C∪D).filter fun w => ∀ u∈B,(colorGraph c k).Adj w u
  by_cases large : 4≤r-B.card
  · obtain ⟨u,hu⟩ := pos
    have sub : W⊆(C.filter fun w => (colorGraph c k).Adj w u) ∪ (D.filter fun w => (colorGraph c k).Adj w u) := by
      intro x hx
      obtain ⟨inside,all⟩ := mem_filter.mp hx
      exact (mem_union.mp inside).elim (fun h => mem_union_left _ (mem_filter.mpr ⟨h,all _ hu⟩))
        (fun h => mem_union_right _ (mem_filter.mpr ⟨h,all _ hu⟩))
    exact (card_le_card sub).trans ((card_union_le ..).trans ((Nat.add_le_add (capC u hu) (capD u hu)).trans large))
  · have lim := Nat.choose_le_choose 2 (show r-B.card+1≤4 by omega)
    have few : (r-B.card+1).choose 2<r-1 := by
      have six : (4:ℕ).choose 2=6 := by decide
      omega
    exact common_neighbors_of_large_clique hb few B W (Nat.add_sub_of_le size) cl (dis.mono_right (filter_subset ..))
      (fun w hw => (mem_filter.mp hw).2)

end Erdos617
