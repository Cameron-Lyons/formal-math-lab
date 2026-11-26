module

public import Erdos617.LocalPaletteEnergy

@[expose] public section

namespace Erdos617

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}

theorem balanced_pointClique_le (hr : 2 ≤ r) (c : Sym2 V → Fin r) (hb : Balanced c)
    (k : Fin r) (x : V) : pointClique (colorGraph c k) x ≤ r := by
  obtain ⟨C,_,hC⟩ := exists_pointClique (colorGraph c k) x
  obtain ⟨j,hj⟩ : (univ.erase k).Nonempty := card_pos.mp (by simp; omega)
  have hind : (colorGraph c j).IsIndepSet (C : Set V) := fun _ hy _ hz hne he =>
    (mem_erase.mp hj).1 (he.2.symm.trans (hC.isClique hy hz hne).2)
  rw [←hC.card_eq]
  exact hind.card_le_indepNum.trans (balanced_indepNum_le c hb j)

/-- The total shortfall from an r-clique through every vertex in every color. -/
theorem global_clique_deficit (hr : 2 ≤ r) (hn : Fintype.card V = r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    (∑ x : V, ∑ j, (r-pointClique (colorGraph c j) x))+2*Fintype.card V+r ≤
      r*Fintype.card V+2 := by
  classical
  let n := Fintype.card V
  let w (j : Fin r) (x : V) := pointClique (colorGraph c j) x
  let d (j : Fin r) := ∑ x, (colorGraph c j).degree x
  have per (j : Fin r) : 2*r*n+2*r+1 ≤ d j+n+∑ x,w j x :=
    clique_energy_floor _ (balanced_indepNum_le c hb j) (by simpa [pow_two] using hn)
  have total := sum_le_sum (s:=univ) fun j _ => per j
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id] at total
  have degrees : (∑ j,d j) = n*(n-1) := sum_palette_degrees c
  have costs (j : Fin r) : (∑ x, (r-w j x))+(∑ x,w j x)=n*r := by
    rw [←sum_add_distrib]
    calc
      _ = ∑ _ : V,r := sum_congr rfl (fun x _ => Nat.sub_add_cancel (balanced_pointClique_le hr c hb j x))
      _ = n*r := by simp [n]
  have cost := sum_congr (s₁:=univ) rfl fun j _ => costs j
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,Nat.cast_id] at cost
  change (∑ x : V, ∑ j, (r-w j x))+2*n+r ≤ r*n+2
  rw [sum_comm]
  have eq : n-1=r*r := by simp [n,hn,pow_two]
  rw [degrees,eq] at total
  change n=r^2+1 at hn
  nlinarith only [total,cost,hn]

/-- The colors in which x lies in a monochromatic r-clique. -/
noncomputable def fullColors (c : Sym2 V → Fin r) (x : V) : Finset (Fin r) := by
  classical
  exact univ.filter fun j => ∃ C : Finset V, x∈C ∧ (colorGraph c j).IsNClique r C

theorem mem_fullColors (c : Sym2 V → Fin r) (x : V) (j : Fin r) :
    j ∈ fullColors c x ↔ ∃ C : Finset V, x∈C ∧ (colorGraph c j).IsNClique r C := by
  classical
  simp [fullColors]

private theorem fullColors_count (c : Sym2 V → Fin r) (x : V) :
    r ≤ (∑ j, (r-pointClique (colorGraph c j) x))+(fullColors c x).card := by
  classical
  have per (j : Fin r) : 1 ≤ (r-pointClique (colorGraph c j) x) +
      (if j∈fullColors c x then 1 else 0) := by
    split
    · omega
    · rename_i hj
      by_contra! low
      obtain ⟨C,hx,hC⟩ := exists_pointClique (colorGraph c j) x
      have le : r ≤ C.card := by rw [hC.card_eq]; omega
      by_cases hr : r=0
      · exact Fin.elim0 (hr ▸ j)
      have le' : ({x} : Finset V).card ≤ r := by simp; omega
      obtain ⟨B,hxB,hBC,hB⟩ := exists_subsuperset_card_eq (singleton_subset_iff.mpr hx) le' le
      exact hj ((mem_fullColors ..).mpr ⟨B,singleton_subset_iff.mp hxB,hC.isClique.subset hBC,hB⟩)
  have m := sum_le_sum (s:=univ) fun j _ => per j
  simpa [sum_add_distrib] using m

/-- An unrestricted lower bound on incidences between vertices and colors
of monochromatic cliques of order r. -/
theorem full_color_incidences (hr : 3 ≤ r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) :
    2*Fintype.card V+r ≤ (∑ x : V,(fullColors c x).card)+2 := by
  have total := sum_le_sum (s:=univ) fun x _ => fullColors_count c x
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul] at total
  have cap := global_clique_deficit (by omega) hn c hb
  nlinarith only [cap,total]

/-- A single vertex in an arbitrary counterexample lies on full cliques
of at least three different colors. -/
theorem exists_three_full_colors (hr : 3 ≤ r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (hb : Balanced c) : ∃ x : V, 3 ≤ (fullColors c x).card := by
  by_contra! h
  have upper := sum_le_sum (s:=univ) (g:=fun _ : V => 2) fun x _ => Nat.le_of_lt_succ (h x)
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at upper
  have lower := full_color_incidences hr hn c hb
  omega

/-- The missing-color conclusion when every vertex is contained in full
cliques of at most two colors. -/
theorem missing_of_at_most_two_full_colors (hr : 3 ≤ r) (hn : Fintype.card V=r^2+1)
    (c : Sym2 V → Fin r) (h : ∀ x : V,(fullColors c x).card ≤ 2) :
    ∃ (S : Finset V) (k : Fin r), S.card=r+1 ∧
      ∀ u ∈ S, ∀ v ∈ S, u≠v → c s(u,v)≠k := by
  by_contra fail
  obtain ⟨x,hx⟩ := exists_three_full_colors hr hn c (balanced_of_no_witness c fail)
  exact (Nat.not_succ_le_self 2) (hx.trans (h x))

end Erdos617
