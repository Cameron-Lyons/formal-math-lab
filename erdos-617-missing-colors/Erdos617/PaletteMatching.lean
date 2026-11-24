import Erdos617.OddIntersection
import Erdos617.MatchingCertificate
import Erdos617.SmallRange

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} {r t : ℕ}

/-- A group is represented on every set of the required size. -/
def HitsPalette (c : Sym2 V → Fin r) (t : ℕ) (B : Finset (Fin r)) : Prop :=
  ∀ S : Finset V, S.card=t+1 → ∃ x∈S, ∃ y∈S, x≠y ∧ c s(x,y)∈B

/-- Merging disjoint groups that each hit every (t+1)-set realizes a
balanced t-coloring. The labels assigned to the groups are distinct. -/
theorem balanced_merge_of_disjoint_groups {ι : Type*} [Fintype ι] (ht : 0<t)
    (hn : Fintype.card ι=t) (c : Sym2 V → Fin r) (B : ι → Finset (Fin r))
    (hd : Pairwise (fun i j => Disjoint (B i) (B j))) (hh : ∀ i, HitsPalette c t (B i)) :
    ∃ f : Fin r → Fin t, Balanced (f ∘ c) := by
  classical
  let e := Fintype.equivFinOfCardEq hn
  let f (k : Fin r) := if h : ∃ i, k∈B i then e h.choose else ⟨0,ht⟩
  have good (i : ι) (k : Fin r) (hki : k∈B i) : f k=e i := by
    have h : ∃ j, k∈B j := ⟨i,hki⟩
    have eq : h.choose=i := by
      by_contra ne
      exact disjoint_left.mp (hd ne) h.choose_spec hki
    simp [f,h,eq]
  refine ⟨f,fun S hs k => ?_⟩
  obtain ⟨x,hx,y,hy,hxy,hcolor⟩ := hh (e.symm k) S hs
  exact ⟨x,hx,y,hy,hxy,(good _ _ hcolor).trans (e.apply_symm_apply k)⟩

/-- The other colors after keeping i and j as the two designated groups. -/
def remainingPalette (i j : Fin r) := (univ.erase i).erase j

private def pairLabels {i j : Fin r} (e : Sym2 (remainingPalette i j)) : Finset (Fin r) :=
  e.toFinset.map (Function.Embedding.subtype (· ∈ remainingPalette i j))

private def mergeGraph (c : Sym2 V → Fin r) (t : ℕ) (i j : Fin r) :
    SimpleGraph (remainingPalette i j) where
  Adj a b := a≠b ∧ HitsPalette c t {a.val,b.val}
  symm.symm a b h := ⟨h.1.symm,by simpa [pair_comm] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem merge_using_matching (ht : 3 ≤ t) (c : Sym2 V → Fin r) {i j : Fin r} (hij : i≠j)
    (hi : HitsPalette c t {i}) (hj : HitsPalette c t {j})
    (F : Finset (Sym2 (remainingPalette i j))) (hn : F.card=t-2)
    (he : ∀ e ∈ F,e∈(mergeGraph c t i j).edgeSet)
    (hd : (↑F : Set (Sym2 (remainingPalette i j))).PairwiseDisjoint Sym2.toFinset) :
    ∃ f : Fin r → Fin t, Balanced (f ∘ c) := by
  classical
  let ι := (Fin 2) ⊕ F
  let B (u : ι) : Finset (Fin r) := match u with
    | .inl a => if a=0 then {i} else {j}
    | .inr e => pairLabels e.val
  have inside (e : F) : B (.inr e) ⊆ remainingPalette i j := by
    intro k hk
    obtain ⟨k,_,rfl⟩ := mem_map.mp hk
    exact k.prop
  have iout : i∉remainingPalette i j := by simp [remainingPalette]
  have jout : j∉remainingPalette i j := by simp [remainingPalette]
  have cross (a : Fin 2) (e : F) : Disjoint (B (.inl a)) (B (.inr e)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have mem := inside e hy
    fin_cases a <;> simp [B] at hx <;> subst x <;> contradiction
  apply balanced_merge_of_disjoint_groups (ι:=ι) (by omega) (by
    simp only [ι,Fintype.card_sum,Fintype.card_fin,Fintype.card_coe,hn]
    omega) c B
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all [B,disjoint_singleton_left,Ne.symm hij]
      | inr b => exact cross a b
    | inr a =>
      cases b with
      | inl b => exact (cross b a).symm
      | inr b =>
        have ne : a.val≠b.val := fun eq => hab (congrArg Sum.inr (Subtype.ext eq))
        exact (Finset.disjoint_map _).mpr (hd a.prop b.prop ne)
  · intro a
    cases a with
    | inl b => fin_cases b <;> simp [B,hi,hj]
    | inr e =>
      have good := he _ e.prop
      obtain ⟨a,b,eq⟩ := Sym2.exists.mp (show ∃ z : Sym2 (remainingPalette i j),e.val=z from ⟨_,rfl⟩)
      rw [eq,mem_edgeSet] at good
      simpa [B,pairLabels,eq,Sym2.toFinset_mk_eq] using good.2

/-- Deleting X leaves separated sets of foreign colors. Pairs crossing two
blocks can be avoided together, and the odd blocks outnumber X by at least three. -/
def HasPaletteBarrier (c : Sym2 V → Fin r) (t : ℕ) (i j : Fin r) : Prop :=
  ∃ (X : Finset (remainingPalette i j)) (P : Finset (Finset (remainingPalette i j))),
        P.biUnion id=univ \ X ∧ (↑P : Set (Finset (remainingPalette i j))).PairwiseDisjoint id ∧
        X.card+3 ≤ (P.filter (fun A => Odd A.card)).card ∧
        ∀ A∈P, ∀ B∈P, A≠B → ∀ a∈A, ∀ b∈B,
          ∃ S : Finset V, S.card=t+1 ∧ ∀ x∈S, ∀ y∈S, x≠y →
            c s(x,y)≠a.val ∧ c s(x,y)≠b.val

/-- If two colors already hit all (t+1)-sets at an odd endpoint, either their
remaining colors can be merged in pairs to produce a smaller balanced coloring,
or a Tutte–Berge separator splits them into at least three more odd blocks
than the number of deleted colors. Every pair from different blocks is jointly
absent on some (t+1)-set. -/
theorem palette_matching_or_barrier (ht : 3 ≤ t) (hr : r=2*t-1) (c : Sym2 V → Fin r)
    {i j : Fin r} (hij : i≠j) (hi : HitsPalette c t {i}) (hj : HitsPalette c t {j}) :
    (∃ f : Fin r → Fin t, Balanced (f ∘ c)) ∨
      HasPaletteBarrier c t i j := by
  classical
  by_cases yes : ∃ f : Fin r → Fin t, Balanced (f ∘ c)
  · exact Or.inl yes
  right
  let G := mergeGraph c t i j
  have cap (F : Finset (Sym2 (remainingPalette i j))) (he : ∀ e∈F,e∈G.edgeSet)
      (hd : (↑F : Set (Sym2 (remainingPalette i j))).PairwiseDisjoint Sym2.toFinset) : F.card ≤ t-3 := by
    by_contra! high
    obtain ⟨M,sub,hm⟩ := exists_subset_card_eq (s:=F) (show t-2 ≤ F.card by omega)
    exact yes (merge_using_matching ht c hij hi hj M hm (fun e h => he e (sub h)) (fun _ ha _ hb ne => hd (sub ha) (sub hb) ne))
  obtain ⟨X,P,cover,dis,links,count⟩ := matching_certificate G (t-3) cap
  have size : Fintype.card (remainingPalette i j)=r-2 := by
    have hji : j∈(univ.erase i) := mem_erase.mpr ⟨hij.symm,mem_univ _⟩
    calc
      _ = (remainingPalette i j).card := Fintype.card_coe _
      _ = _ := by
        unfold remainingPalette
        rw [card_erase_of_mem hji,card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]
        omega
  have parts := card_biUnion dis
  rw [cover,card_sdiff_of_subset (subset_univ _),card_univ,size] at parts
  have split (A : Finset (remainingPalette i j)) (_ : A∈P) :
      A.card=2*(A.card/2)+(if Odd A.card then 1 else 0) := by
    by_cases odd : Odd A.card <;> simp [odd] <;> rw [Nat.odd_iff] at odd <;> omega
  have total := sum_congr rfl split
  simp only [sum_add_distrib,←mul_sum,sum_boole,Nat.cast_id] at total
  have xcap := le_trans (card_le_univ X) size.le
  refine ⟨X,P,cover,dis,?_,?_⟩
  · simp only [id_eq] at parts
    change (∑ A∈P,A.card)=2*(∑ A∈P,A.card/2)+(P.filter (fun A => Odd A.card)).card at total
    have cnt : r-2-X.card=2*(∑ A∈P,A.card/2)+(P.filter (fun A => Odd A.card)).card := parts.trans total
    omega
  intro A hA B hB ne a ha b hb
  have distinct : a≠b := by rintro rfl; exact disjoint_left.mp (dis hA hB ne) ha hb
  have off {C : Finset (remainingPalette i j)} (hC : C∈P) {k} (hk : k∈C) : k∉X :=
    (mem_sdiff.mp (biUnion_subset.mp cover.le C hC hk)).2
  have bad : ¬ HitsPalette c t {a.val,b.val} := by
    intro hit
    obtain ⟨D,hD,haD,hbD⟩ := links a b (off hA ha) (off hB hb) ⟨distinct,hit⟩
    have eq {Z : Finset (remainingPalette i j)} (hZ : Z∈P) {x} (hx : x∈Z) (hh : x∈D) : Z=D := by
      by_contra nn
      exact disjoint_left.mp (dis hZ hD nn) hx hh
    exact ne ((eq hA ha haD).trans (eq hB hb hbD).symm)
  unfold HitsPalette at bad
  push Not at bad
  obtain ⟨S,hS,hmiss⟩ := bad
  exact ⟨S,hS,fun x hx y hy hxy => by simpa [not_or] using hmiss x hx y hy hxy⟩

variable [DecidableEq V]

theorem single_hit_of_rank {U : Finset V} (c : Sym2 V → Fin r) (i : Fin r)
    (hα : rankOn (colorGraph c i) U ≤ t) :
    HitsPalette (fun e : Sym2 U => c (e.map Subtype.val)) t {i} := by
  classical
  intro S hn
  by_contra! miss
  let f := Function.Embedding.subtype (·∈U)
  have ind : (colorGraph c i).IsIndepSet (S.map f : Finset V) := by
    intro x hx y hy hxy he
    obtain ⟨xx,hxs,rfl⟩ := mem_map.mp hx
    obtain ⟨yy,hys,rfl⟩ := mem_map.mp hy
    have eq := he.2
    exact miss xx hxs yy hys (fun e => hxy (congrArg f e)) (by simpa [f] using eq)
  have sub : S.map f ⊆ U := fun x hx => by obtain ⟨x,_,rfl⟩ := mem_map.mp hx; exact x.prop
  have le := (card_le_rankOn _ sub ind).trans hα
  rw [card_map,hn] at le
  omega

/-- At the odd endpoint, the two guaranteed colors can be completed by pairing
other colors unless the original palette contains a Tutte–Berge barrier on the
very same smaller vertex set. -/
theorem odd_endpoint_merge_or_barrier [Fintype V] {s : ℕ} (hs : 2 ≤ s) (hr : r=2*s+1)
    (hn : Fintype.card V=r^2+1) (c : Sym2 V → Fin r) (hb : Balanced c)
    (hsmall : ∀ (k : Fin r) (a : ℕ), a ≤ s → ∀ W : Finset V, ¬MinimalObstruction c k a W) :
    ∃ (i j : Fin r) (U : Finset V), i≠j ∧ U.card=(s+1)^2+1 ∧
      let d (e : Sym2 U) := c (e.map Subtype.val)
      HitsPalette d (s+1) {i} ∧ HitsPalette d (s+1) {j} ∧
      ((∃ f : Fin r → Fin (s+1), Balanced (f ∘ d)) ∨ HasPaletteBarrier d (s+1) i j) := by
  classical
  obtain ⟨i,j,A,B,_,_,hij,_,_,_,_,_,_,_,_,_,size,hi,hj⟩ := odd_endpoint_intersection (by omega) hr hn c hb hsmall
  have p := single_hit_of_rank c i hi
  have q := single_hit_of_rank c j hj
  exact ⟨i,j,A∩B,hij,size,p,q,palette_matching_or_barrier (by omega) (by omega) _ hij p q⟩

/-- For a smaller target of three through six colors, the verified small
cases exclude the merger and force the barrier. -/
theorem palette_barrier_of_small_range [Fintype V] (ht : 3≤t) (hs : t≤6) (hr : r=2*t-1)
    (hn : Fintype.card V=t^2+1) (c : Sym2 V → Fin r) {i j : Fin r} (hij : i≠j)
    (hi : HitsPalette c t {i}) (hj : HitsPalette c t {j}) : HasPaletteBarrier c t i j := by
  apply (palette_matching_or_barrier ht hr c hij hi hj).resolve_left
  rintro ⟨f,hb⟩
  obtain ⟨S,k,hS,hfree⟩ := missing_of_at_most_six_colors ht hs hn (f ∘ c)
  obtain ⟨x,hx,y,hy,hxy,he⟩ := hb S hS k
  exact hfree x hx y hy hxy he

end Erdos617
