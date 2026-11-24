import Erdos617.DeletionRank
import Erdos617.LocalPaletteEnergy

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- In a rank-four eight-color obstruction the target color has 143 edges,
maximum degree at most nine, and at most five total units of shortfall from
seven in its through-vertex clique sizes. -/
theorem MinimalObstruction.eight_energy_profile {c : Sym2 V → Fin 8} {k : Fin 8} {S : Finset V}
    (h : MinimalObstruction c k 4 S) (hb : Balanced c) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
    Fintype.card S=33 ∧ (∀ v : S, G.degree v≤9) ∧
      (∑ v : S, (7-pointClique G v)) ≤ 5 ∧ (∀ v : S, pointClique G v≤7) ∧
      G.edgeFinset.card=143 := by
  classical
  intro G
  let H := colorGraph c k
  let cp : Sym2 S → Fin 8 := fun e => c (Sym2.map Subtype.val e)
  have hn : S.card=33 := h.card_eq
  have n : Fintype.card S=33 := (Fintype.card_coe S).trans hn
  obtain ⟨ind,cap,_⟩ := h.point_clique_caps hb (by decide)
  have sum := sum_color_edges cp
  rw [←sum_erase_add _ _ (mem_univ k),n] at sum
  have foreign := h.foreign_edge_sum hb (by decide)
  change (8-1)*(8*Nat.choose 4 2+2*4-1) ≤ ∑ j∈univ.erase k,(colorGraph cp j).edgeFinset.card at foreign
  have slack := h.rank_edge_slack_two hb (by decide) (by decide) (by decide)
  rw [hn,color_blockEdges_eq] at slack
  change 8*33+2≤(colorGraph cp k).edgeFinset.card+(Nat.choose 8 2+1)*4+(8-1) at slack
  norm_num [Nat.choose] at sum foreign slack
  have cnt : G.edgeFinset.card=143 := by change (colorGraph cp k).edgeFinset.card=143; omega
  have cost := clique_energy_floor (a:=4) (q:=8) G ind (by omega)
  rw [G.sum_degrees_eq_twice_card_edges,cnt,n] at cost
  have both : (∑ v:S,(7-pointClique G v))+(∑ v:S, pointClique G v) = 33*7 := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ : S, 7 := sum_congr rfl (fun x _ => Nat.sub_add_cancel (cap x))
      _ = 33*7 := by simp [hn]
  refine ⟨n,?_,by omega,cap,cnt⟩
  intro x
  let A := S.erase x.val
  have sep := h.erase_rank_inseparable hb (by decide) (by decide) x.prop
  have eq : rankOn H A=4 := ((h.rank_inseparable (by decide)).rank_erase x.prop (by omega)).trans (h.rank_eq (by decide))
  have sz : A.card=32 := by dsimp [A]; rw [card_erase_of_mem x.prop, hn]
  have low := rank_density H A sep 8
  have strict : 8*A.card < blockEdges H A+(Nat.choose 8 2+1)*rankOn H A+(8-1) := by
    refine lt_of_le_of_ne low (fun tight => ?_)
    obtain ⟨C,sub,hC⟩ := exists_clique_of_saturated_rank_density_eq H A sep 8 (by decide) (by omega)
      (by rw [sz,eq]) tight
    exact h.no_clique hb (by decide) C (sub.trans (erase_subset ..)) hC
  rw [sz,eq] at strict
  norm_num [Nat.choose] at strict
  have edges := blockEdges_erase_add H S x.val x.prop
  have whole : blockEdges H S=143 := (color_blockEdges_eq S c k).trans cnt
  rw [whole] at edges
  change blockEdges H A+(S.filter (H.Adj x.val)).card=143 at edges
  let incl := Function.Embedding.subtype (· ∈ S)
  have image : (G.neighborFinset x).map incl=S.filter (H.Adj x.val) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      have e := (G.mem_neighborFinset x u).mp hu
      exact mem_filter.mpr ⟨u.prop,fun eq => e.1 (Subtype.ext eq),e.2⟩
    · intro hy
      obtain ⟨hy,e⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hy⟩,(G.mem_neighborFinset ..).mpr ⟨fun eq => e.1 (congrArg Subtype.val eq), e.2⟩,rfl⟩
  have deg := congrArg Finset.card image
  rw [card_map,card_neighborFinset_eq_degree] at deg
  omega

/-- In an eight-color rank-four obstruction, two distinct nonneighbors in
the target color have at most two common neighbors. -/
theorem MinimalObstruction.eight_common_neighbors {c : Sym2 V → Fin 8} {k : Fin 8} {S : Finset V}
    (h : MinimalObstruction c k 4 S) (hb : Balanced c) :
    let G := colorGraph (fun e : Sym2 S => c (Sym2.map Subtype.val e)) k
    ∀ x y : S, x ≠ y → ¬G.Adj x y → (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 2 := by
  classical
  intro G x y xy nxy
  let H := colorGraph c k
  let D := G.neighborFinset x ∪ G.neighborFinset y
  let R := (insert x (insert y D))ᶜ
  let incl := Function.Embedding.subtype (·∈S)
  let A := R.map incl
  have sub : A⊆S := fun _ hw => R.property_of_mem_map_subtype hw
  have data {w : V} (hw : w∈A) : x.val≠w ∧ y.val≠w ∧ ¬H.Adj x.val w ∧ ¬H.Adj y.val w := by
    obtain ⟨a,ha,rfl⟩ := mem_map.mp hw
    change a∈(insert x (insert y (G.neighborFinset x ∪ G.neighborFinset y)))ᶜ at ha
    simp only [mem_compl,mem_insert,mem_union,mem_neighborFinset,not_or] at ha
    exact ⟨fun e => ha.1 (Subtype.ext e).symm,fun e => ha.2.1 (Subtype.ext e).symm,
      fun e => ha.2.2.1 ⟨fun z => ha.1 z.symm,e.2⟩,fun e => ha.2.2.2 ⟨fun z => ha.2.1 z.symm,e.2⟩⟩
  have xx : x.val≠y.val := fun e => xy (Subtype.ext e)
  have he : ¬H.Adj x.val y.val := fun e => nxy ⟨xy,e.2⟩
  obtain ⟨J,hJ,ind,eq⟩ := exists_max_indep H A
  have xJ : x.val∉J := fun hx => (data (hJ hx)).1 rfl
  have yJ : y.val∉insert x.val J := by
    rw [mem_insert,not_or]; exact ⟨xx.symm,fun hy => (data (hJ hy)).2.1 rfl⟩
  have ia := independent_insert_of_nonadjacent H ind x.val (fun _ hu => (data (hJ hu)).2.2.1)
  have ib := independent_insert_of_nonadjacent H ia y.val (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact fun e => he e.symm
    · exact (data (hJ hz)).2.2.2)
  have rc := card_le_rankOn H (insert_subset y.prop (insert_subset x.prop (hJ.trans sub))) ib
  rw [card_insert_of_notMem yJ,card_insert_of_notMem xJ,eq] at rc
  have rce : rankOn H S=4 := h.rank_eq (by decide)
  have bound := h.rank_two_card_lt hb (by decide) (by decide) sub (by change rankOn H A≤2; omega)
  have sizes : A.card=R.card := card_map _
  have ⟨n,deg,_⟩ := h.eight_energy_profile hb
  have nx : x∉insert y D := by simp [D,xy,nxy,G.adj_comm y x]
  have ny : y∉D := by simp [D,nxy]
  have total : R.card+(D.card+2)=33 := by
    rw [show D.card+2=(insert x (insert y D)).card by rw [card_insert_of_notMem nx,card_insert_of_notMem ny]]
    simpa only [R, card_compl_add_card] using n
  have degsum := card_union_add_card_inter (G.neighborFinset x) (G.neighborFinset y)
  change D.card+_=_+_ at degsum
  rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at degsum
  have dx : G.degree x≤9 := deg x
  have dy : G.degree y≤9 := deg y
  omega

end Erdos617
