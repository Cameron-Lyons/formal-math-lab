module

public import Erdos617.LineMultiplicity
public import Erdos617.OddBags

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] {r : ℕ}

private theorem star_inter_eq (p : V → Sym2 L) {i j : L} (hij : i ≠ j) :
    lineStar p i ∩ lineStar p j = univ.filter (fun x => p x=s(i,j)) := by
  ext x
  simp only [lineStar,mem_inter,mem_filter,mem_univ,true_and,Sym2.mem_toFinset]
  exact Sym2.mem_and_mem_iff hij

/-- A positive endpoint multiplicity forces the two-star union above the vertex-degree
threshold. The product of the two deficits bounds the weighted excess of that union. -/
theorem line_pair_budget (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) {i j : L} (hij : i ≠ j)
    (hm : 0 < lineMultiplicity p s(i,j)) :
    let b := (lineStar p i).card
    let d := (lineStar p j).card
    let m := lineMultiplicity p s(i,j)
    r+1 ≤ b+d-m ∧ (m-1)*(r-m-(r-b)-(r-d)) ≤ (r-b)*(r-d) := by
  classical
  let A := lineStar p i
  let B := lineStar p j
  let m := lineMultiplicity p s(i,j)
  have hi : (A∩B).card=m := congrArg card (star_inter_eq p hij)
  have hpos : (A∩B).Nonempty := card_pos.mp (hi ▸ hm)
  obtain ⟨x,hx⟩ := hpos
  have hxf : x∈univ.filter (fun y => p y=s(i,j)) := (star_inter_eq p hij) ▸ hx
  have hxpair : p x=s(i,j) := (mem_filter.mp hxf).2
  have hsub : univ.filter ((colorGraph c k).Adj x) ⊆ (A∪B).erase x := by
    intro y hy
    have ha := (mem_filter.mp hy).2
    obtain ⟨a,hax,hay⟩ := not_disjoint_iff.mp ((rep.adj x (mem_univ _) y (mem_univ _) ha.ne).mp ha)
    rw [hxpair, Sym2.toFinset_mk_eq] at hax
    refine mem_erase.mpr ⟨ha.ne.symm,?_⟩
    rcases mem_insert.mp hax with e | e
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,e ▸ hay⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,mem_singleton.mp e ▸ hay⟩)
  have deg := (line_minimal_obstruction_top hr hn c hb k p rep).degree_ge x (mem_univ _)
  have hg := deg.trans (card_le_card hsub)
  rw [card_erase_of_mem (mem_union_left _ (mem_inter.mp hx).1)] at hg
  have hbig : r+1 ≤ (A∪B).card := by omega
  have hp := foreign_pair_budget c hb k (A∪B) ((A\B) ×ˢ (B\A)) (by
    intro x hx y hy hxy hcol
    have h1 : ¬(x∈A ∧ y∈A) := fun h => hcol ((rep.star_isClique i) h.1 h.2 hxy).2
    have h2 : ¬(x∈B ∧ y∈B) := fun h => hcol ((rep.star_isClique j) h.1 h.2 hxy).2
    simp only [mem_union,mem_product,mem_sdiff] at *
    grind)
  rw [card_product] at hp
  have hui := card_union_add_card_inter A B
  have hA := card_inter_add_card_sdiff A B
  have hB := card_inter_add_card_sdiff B A
  rw [inter_comm B A,hi] at hB
  rw [hi] at hA hui
  obtain ⟨_,_,_,hsize,_⟩ := line_label_data hr hn c hb k p rep
  have ha : A.card ≤ r := hsize i
  have hb' : B.card ≤ r := hsize j
  have hδ : r-A.card+A.card=r := Nat.sub_add_cancel ha
  have hε : r-B.card+B.card=r := Nat.sub_add_cancel hb'
  let g := (A∪B).card-r
  have hg' : (A∪B).card=g+r := by dsimp [g]; omega
  have hg1 : r-m-(r-A.card)-(r-B.card)=g := by dsimp [g]; omega
  have h1 : (A\B).card = g+(r-B.card) := by omega
  have h2 : (B\A).card = g+(r-A.card) := by omega
  have h3 : r-1 = (m-1)+g+(r-A.card)+(r-B.card) := by change 0<m at hm; omega
  change r+1 ≤ A.card+B.card-m ∧ (m-1)*(r-m-(r-A.card)-(r-B.card)) ≤ (r-A.card)*(r-B.card)
  refine ⟨by omega,?_⟩
  rw [hg1]
  rw [hg', h1, h2, h3] at hp
  nlinarith only [hp]

/-- For distinct unordered pairs, the sum of endpoint-weight products is at
most the number of pairs of distinct weight units. -/
private theorem weighted_pair_sum {L : Type*} [DecidableEq L] (C : Finset L)
    (d : L → ℕ) (w : Sym2 L → ℕ) (E : Finset (Sym2 L))
    (hE : ∀ e∈E, ∃ i∈C, ∃ j∈C, i≠j ∧ e=s(i,j))
    (hw : ∀ i∈C, ∀ j∈C, i≠j → w s(i,j) ≤ d i*d j) :
    2*(∑ e∈E, w e)+(∑ i∈C, d i) ≤ (∑ i∈C, d i)^2 := by
  classical
  induction C using Finset.induction_on generalizing E with
  | empty =>
    have he : E=∅ := eq_empty_iff_forall_notMem.mpr (by simpa using hE)
    simp [he]
  | insert a C ha ih =>
    let F := E.filter fun e => a∈e
    let T := E.filter fun e => a∉e
    have hT : ∀ e∈T, ∃ i∈C, ∃ j∈C, i≠j ∧ e=s(i,j) := by
      intro e he
      obtain ⟨hg,hn⟩ := mem_filter.mp he
      obtain ⟨i,hi,j,hj,hij,rfl⟩ := hE _ hg
      have hai : a≠i := by rintro rfl; exact hn (Sym2.mem_mk_left ..)
      have haj : a≠j := by rintro rfl; exact hn (Sym2.mem_mk_right ..)
      exact ⟨i,(mem_insert.mp hi).resolve_left hai.symm,j,(mem_insert.mp hj).resolve_left haj.symm,hij,rfl⟩
    have hinner := ih T hT (fun i hi j hj => hw i (mem_insert_of_mem hi) j (mem_insert_of_mem hj))
    let enc := Sym2.mkEmbedding a
    have cover : F ⊆ C.map enc := by
      intro e he
      obtain ⟨hg,hm⟩ := mem_filter.mp he
      obtain ⟨i,hi,j,hj,hij,rfl⟩ := hE _ hg
      rcases Sym2.mem_iff.mp hm with h | h
      · subst i
        exact mem_map.mpr ⟨j,(mem_insert.mp hj).resolve_left hij.symm,rfl⟩
      · subst j
        exact mem_map.mpr ⟨i,(mem_insert.mp hi).resolve_left hij,Sym2.eq_swap⟩
    have hcross : (∑ e∈F,w e) ≤ d a*(∑ i∈C,d i) := by
      calc
        _ ≤ ∑ e∈C.map enc,w e := sum_le_sum_of_subset cover
        _ = ∑ i∈C,w s(a,i) := by rw [sum_map]; rfl
        _ ≤ ∑ i∈C,d a*d i := sum_le_sum fun i hi =>
          hw a (mem_insert_self ..) i (mem_insert_of_mem hi) (fun h => ha (h ▸ hi))
        _ = _ := (mul_sum ..).symm
    have split : (∑ e∈F,w e)+(∑ e∈T,w e)=∑ e∈E,w e :=
      sum_filter_add_sum_filter_not E (fun e => a∈e) w
    have hs : d a ≤ d a^2 := Nat.le_self_pow (by decide) _
    rw [sum_insert ha]
    nlinarith only [hinner,hcross,split,hs]

/-- For some repeated pair, three times its multiplicity exceeds twice the
available degree after the star deficits of its two endpoints are deducted. -/
theorem exists_heavy_parallel_pair_strict (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) (C : Finset L)
    (hc : C.card ≤ 2*r+1) (hcover : ∀ x, (p x).toFinset ⊆ C) :
    ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ 2 ≤ lineMultiplicity p s(i,j) ∧
      2*r < 2*((r-(lineStar p i).card)+(r-(lineStar p j).card))+3*lineMultiplicity p s(i,j) := by
  classical
  let d (i : L) := r-(lineStar p i).card
  let m := lineMultiplicity p
  let w (e : Sym2 L) := (m e).choose 2
  have doubleCount (e : Sym2 L) : 2*w e = m e*(m e-1) := by
    change 2*(m e).choose 2 = _
    have h := twice_choose_two (m e)
    rcases Nat.eq_zero_or_pos (m e) with he | hp
    · simp [he] at *
    · have cancel := congrArg ((m e) * ·) (Nat.sub_add_cancel (show 1≤m e by omega))
      rw [Nat.mul_add,Nat.mul_one] at cancel
      omega
  let E := univ.image p
  have hE (e : Sym2 L) (he : e ∈ E) : ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ e=s(i,j) := by
    obtain ⟨x, _, rfl⟩ := mem_image.mp he
    obtain ⟨i,j,eq⟩ := Sym2.exists.mp (show ∃ e : Sym2 L, p x=e from ⟨_,rfl⟩)
    have ends : {i,j} ⊆ C := by simpa [eq,Sym2.toFinset_mk_eq] using hcover x
    exact ⟨i,ends (by simp),j,ends (by simp),by simpa [eq,Sym2.mk_isDiag_iff] using rep.distinct x (mem_univ _),eq⟩
  by_contra noHeavy
  have hw (i : L) (hi : i ∈ C) (j : L) (hj : j ∈ C) (hij : i ≠ j) : w s(i,j) ≤ d i*d j := by
    by_cases two : 2 ≤ m s(i,j)
    · have cap : 2*(d i+d j)+3*m s(i,j) ≤ 2*r := le_of_not_gt (fun h => noHeavy ⟨i,hi,j,hj,hij,two,h⟩)
      have hp := (line_pair_budget hr hn c hb k p rep hij (by change 0 < m s(i,j); omega)).2
      change (m s(i,j)-1)*(r-m s(i,j)-d i-d j) ≤ d i*d j at hp
      have le : m s(i,j) ≤ 2*(r-m s(i,j)-d i-d j) := by omega
      have upper := Nat.mul_le_mul_left (m s(i,j)-1) le
      nlinarith only [upper,hp,doubleCount s(i,j)]
    · have small : m s(i,j)-1=0 := by omega
      have eq := doubleCount s(i,j)
      rw [small,Nat.mul_zero] at eq
      omega
  have weighted := weighted_pair_sum C d w E hE hw
  obtain ⟨_,_,_,size,_⟩ := line_label_data hr hn c hb k p rep
  have count := sum_stars C p _ rep hcover
  rw [hn] at count
  change ∑ i∈C,(lineStar p i).card=2*(r^2+1) at count
  have total := sum_congr (s₁:=C) rfl (g:=fun _ => r) (fun i _ =>
    show d i + (lineStar p i).card = r from Nat.sub_add_cancel (size i))
  rw [sum_add_distrib,count,sum_const,nsmul_eq_mul] at total
  simp only [Nat.cast_id] at total
  have num := Nat.mul_le_mul_right r hc
  rw [show (2*r+1)*r=2*r^2+r by ring] at num
  have dsum : (∑ i∈C,d i) ≤ r-2 := by omega
  have lower := line_parallel_excess hr hn c hb k p rep
  change (r-2)*(r+1) ≤ ∑ e∈E,m e*(m e-1) at lower
  simp_rw [← doubleCount, ← mul_sum] at lower
  have sq := Nat.pow_le_pow_left dsum 2
  have strict : (r-2)^2 < (r-2)*(r+1) := by
    rw [pow_two]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

/-- A repeated endpoint pair has twice its multiplicity plus its two star
deficits above the palette size. -/
theorem exists_heavy_parallel_pair (hr : 3 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) (k : Fin r) (p : V → Sym2 L)
    (rep : LineRepresentation (colorGraph c k) univ p) (C : Finset L)
    (hc : C.card ≤ 2*r+1) (hcover : ∀ x, (p x).toFinset ⊆ C) :
    ∃ i ∈ C, ∃ j ∈ C, i ≠ j ∧ 2 ≤ lineMultiplicity p s(i,j) ∧
      r < (r-(lineStar p i).card)+(r-(lineStar p j).card)+2*lineMultiplicity p s(i,j) := by
  obtain ⟨i,hi,j,hj,hij,hm,hs⟩ := exists_heavy_parallel_pair_strict hr hn c hb k p rep C hc hcover
  exact ⟨i,hi,j,hj,hij,hm,by omega⟩

end Erdos617
