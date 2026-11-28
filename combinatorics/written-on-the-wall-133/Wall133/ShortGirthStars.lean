module

public import Wall133.ShortGirthSeven
public import Wall133.IndependenceCore

@[expose] public section

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {S : Set V} {n d : ℕ}

/-- A vertex has d independent neighbors in the indicated set. -/
structure IndependentCoreStar (G : SimpleGraph V) (S : Set V) (v : V) (d : ℕ) where
  points : Finset V
  card : d ≤ points.card
  independent : G.IsIndepSet (points : Set V)
  inside : ∀ w∈points,w∈S
  adj : ∀ w∈points,G.Adj v w

theorem IndependentCoreStar.options [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {P : Chain G n}
    (A : IndependentCoreStar G S (P.vertex 0) d) (h4 : NoFourCycle G) (hn : 2≤n) :
    ∃ B : ContactOptions P d, (∀ w∈B.points,w∈S) ∧ G.IsIndepSet (B.points : Set V) := by
  classical
  let p := P.vertex 1
  let B := A.points.filter (fun w => w≠p ∧ ¬G.Adj p w)
  have filt {w} : w∈B ↔ w∈A.points ∧ w≠p ∧ ¬G.Adj p w := Finset.mem_filter
  have near := (P.edges (Nat.zero_le _) (by omega : 1≤n)).2 (Or.inl rfl)
  have diff {w} (hw : w∈A.points \ B) : w∈A.points ∧ (w=p ∨ G.Adj p w) := by
    obtain ⟨hA,hB⟩ := Finset.mem_sdiff.mp hw
    exact ⟨hA,by by_contra! h; exact hB (filt.mpr ⟨hA,h⟩)⟩
  have cnt : (A.points \ B).card ≤ 1 := Finset.card_le_one.mpr (by
    intro u hu w hw
    by_contra ne
    obtain ⟨ux,eu|au⟩ := diff hu <;> obtain ⟨wx,ew|aw⟩ := diff hw
    · exact ne (eu.trans ew.symm)
    · exact A.independent ux wx ne (eu ▸ aw)
    · exact A.independent ux wx ne (ew ▸ au.symm)
    · exact ne (h4 near.ne (A.adj _ ux) au (A.adj _ wx) aw))
  have hcard := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ A.points : B ⊆ A.points)
  change (A.points \ B).card+B.card=A.points.card at hcard
  obtain ⟨C,eq⟩ := contact_options_of_eligible P hn h4
    (fun {w} hw => ⟨A.adj _ (filt.mp hw).1,(filt.mp hw).2⟩)
    (by have := A.card; omega : d≤B.card+1)
  refine ⟨C,?_,?_⟩ <;> rw [eq]
  · exact fun w hw => A.inside _ (filt.mp hw).1
  · exact fun w hw z hz ne => A.independent (filt.mp hw).1 (filt.mp hz).1 ne

theorem IndependentCoreStar.ambient [Fintype V] [DecidableRel G.Adj] {v : V}
    (A : IndependentCoreStar G S v d) : d≤G.indepNeighborsCard v := by
  classical
  let H := G.induce (G.neighborSet v)
  let f : (w : V) → w∈A.points → G.neighborSet v := fun w hw => ⟨w,A.adj w hw⟩
  let emb : A.points ↪ G.neighborSet v := ⟨fun w => f w.val w.property,fun w z e => Subtype.ext (congrArg (fun a : G.neighborSet v => a.val) e)⟩
  let I := A.points.attach.map emb
  have ind : H.IsIndepSet (I : Set (G.neighborSet v)) := by
    intro u hu w hw ne
    obtain ⟨a,_,ea⟩ := Finset.mem_map.mp hu
    obtain ⟨b,_,eb⟩ := Finset.mem_map.mp hw
    subst u
    subst w
    exact A.independent a.property b.property (fun e => ne (Subtype.ext e))
  have h := ind.card_le_indepNum (t := I)
  have hc : I.card=A.points.card := by simp [I]
  exact A.card.trans (hc ▸ h)

theorem exists_core_star_of_induced {T : Finset V} [Fintype V] [DecidableRel G.Adj]
    (v : T) (hd : d ≤ (G.induce (T : Set V)).indepNeighborsCard v) :
    Nonempty (IndependentCoreStar G (T : Set V) v.val d) := by
  classical
  let H := G.induce (T : Set V)
  let J := H.induce (H.neighborSet v)
  obtain ⟨I,hI⟩ := exists_isNIndepSet_indepNum (G := J)
  let f : H.neighborSet v ↪ V :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let A := I.map f
  have mem {w} (hw : w ∈ A) := Finset.mem_map.mp hw
  have size : d≤A.card := by
    change d≤J.indepNum at hd
    simpa [A,hI.card_eq] using hd
  refine ⟨⟨A,size,?_,?_,?_⟩⟩
  · intro w hw z hz ne
    obtain ⟨p,hp,rfl⟩ := mem hw
    obtain ⟨q,hq,rfl⟩ := mem hz
    exact hI.isIndepSet hp hq (fun e => ne (congrArg f e))
  · intro w hw
    obtain ⟨a,_,rfl⟩ := mem hw
    exact a.val.property
  · intro w hw
    obtain ⟨a,_,rfl⟩ := mem hw
    exact a.property

theorem exists_four_core_star [Fintype V] [DecidableEq V] [Nonempty V] [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (hav : (4:ℝ)≤l G) :
    ∃ (S : Set V) (v : V), Nonempty (IndependentCoreStar G S v 4) ∧
      ∀ x∈S, Nonempty (IndependentCoreStar G S x 3) := by
  obtain ⟨T,hT,hmin,hsum⟩ := exists_independence_core (k:=4) h4 (by decide) hav
  let H := G.induce (T : Set V)
  have max : ∃ v:T,4≤H.indepNeighborsCard v := by
    by_contra! h
    have u := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset T))
      (by have := hT.to_subtype; exact Finset.univ_nonempty) (fun v _ => h v)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul] at u
    change (∑ v:T,H.indepNeighborsCard v) < T.card*4 at u
    change 4*T.card ≤ ∑ v:T,H.indepNeighborsCard v at hsum
    omega
  obtain ⟨v,hv⟩ := max
  refine ⟨T,v.val,exists_core_star_of_induced v hv,fun x hx => ?_⟩
  exact exists_core_star_of_induced (⟨x,hx⟩ : T) (hmin _)

end Wall133
