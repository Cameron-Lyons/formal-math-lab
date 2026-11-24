import Wall133.Girth
import Wall133.GeodesicRotation

/-!
# Girth-five graphs at small radius

The second contacts of distinct neighbors of the endpoint of a maximal induced
path are at least one index apart. This holds without a two-coloring.
-/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma saturated_degree_five [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hg : 5 ≤ G.egirth) (hp : Chordless p)
    (sat : ∀ w, G.Adj u w → w ∉ p.support →
      ∃ i ≤ p.length, i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    G.degree u - 1 ≤ p.length-2 := by
  classical
  let W := (G.neighborFinset u).erase (p.getVert 1)
  have info (w : W) : G.Adj u w.val ∧ w.val ∉ p.support := by
    obtain ⟨hne,hadj⟩ := Finset.mem_erase.mp w.property
    have ha := (G.mem_neighborFinset _ _).mp hadj
    exact ⟨ha,hp.pending_off_path ha hne⟩
  choose idx hi hz hadj using fun w : W => sat w.val (info w).1 (info w).2
  have hlo (w : W) : 3 ≤ idx w := by
    have := first_blocker (g := 5) hg hp (info w).1 (info w).2 (hi w) (hz w) (hadj w)
    omega
  have gap {w z : W} (hne : w ≠ z) (hle : idx w ≤ idx z) : idx w+1 ≤ idx z := by
    have := separated_blockers (g := 5) hg hp (info w).1 (info z).1 (info w).2 (info z).2
      (fun he => hne (Subtype.ext he)) (by have := hlo w; omega) hle (hi z) (hadj w) (hadj z) (by decide)
    omega
  let code (w : W) : Fin (p.length-2) :=
    ⟨idx w-3,by have := hlo w; have := hi w; omega⟩
  have inj : Function.Injective code := by
    intro w z h
    by_contra hne
    have eq := congrArg Fin.val h
    change idx w-3=idx z-3 at eq
    have := hlo w; have := hlo z
    rcases le_total (idx w) (idx z) with hle|hle
    · have := gap hne hle; omega
    · have := gap (Ne.symm hne) hle; omega
  have count : W.card ≤ p.length-2 := by simpa using Fintype.card_le_of_injective code inj
  exact (show G.degree u-1 ≤ W.card from Finset.pred_card_le_card_erase).trans count

/-- A graph of girth at least five and minimum degree d has an induced path
with at least d+2 vertices. A vertex of larger degree gains another vertex. -/
theorem girth_five_min_degree_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hg : 5 ≤ G.egirth) {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x)
    (a : V) : d+2+(if d < G.degree a then 1 else 0) ≤ G.path := by
  classical
  let start : G.Walk a a := .nil
  have hstart : Chordless start := ⟨Walk.IsPath.nil, by simp [start]⟩
  obtain ⟨u,p,_,_,hp,_,_,sat⟩ := exists_saturated Set.univ start hstart (Set.mem_univ a)
  have hu := saturated_degree_five hg hp (fun w => sat w (Set.mem_univ _))
  have := hmin u
  obtain ⟨z,q,t,_,hq,hlen,hsuf,sat'⟩ := exists_saturated Set.univ p.reverse hp.reverse (Set.mem_univ a)
  have hlen' : q.length=t+p.length := by simpa using hlen
  have hl := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert q
    hq.simple hq.consecutive)
  rw [Walk.length_support] at hl
  split_ifs with hhi
  · by_cases ht : t=0
    · subst t
      have hza : z=a := by simpa using hsuf 0
      have hz := saturated_degree_five hg hq (fun w => sat' w (Set.mem_univ _))
      have : G.degree z = G.degree a := congrArg (fun w => G.degree w) hza
      omega
    · omega
  · omega

/-- Pruning vertices of degree at most half the density threshold produces a
minimum-degree core with a vertex of strictly greater degree. -/
theorem girth_five_density_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [Nonempty V]
    (hg : 5 ≤ G.egirth) {k : ℕ} (hk : 4 ≤ k) (hav : k * Fintype.card V ≤ ∑ v, G.degree v) :
    k/2+4 ≤ G.path := by
  classical
  let m := k/2
  have hcost : 2 * (∑ _ : V, m) ≤ ∑ x, G.degree x := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = (2*m)*Fintype.card V := by ac_rfl
      _ ≤ k*Fintype.card V := Nat.mul_le_mul_right _ (by dsimp [m]; omega)
      _ ≤ _ := hav
  obtain ⟨S,hS,hmin,hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by dsimp [m]; omega) hcost
  let H := G.induce (S : Set V)
  have minH (v : S) : m+1 ≤ H.degree v := hmin v
  have high : ∃ x : S, m+1 < H.degree x := by
    by_contra! h
    have hle := Finset.sum_le_sum (s := Finset.univ) (fun (x : S) _ => h x)
    change 2*(∑ _x ∈ S, m) ≤ ∑ v : S, H.degree v at hsum
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe] at hsum hle
    change 2*(S.card*m) ≤ ∑ x : S, H.degree x at hsum
    change (∑ x : S, H.degree x) ≤ S.card*(m+1) at hle
    have hlt := Nat.mul_lt_mul_of_pos_left (show m+1 < 2*m by dsimp [m]; omega) hS.card_pos
    have eq : S.card*(2*m) = 2*(S.card*m) := by ac_rfl
    omega
  obtain ⟨a,ha⟩ := high
  have hg' : 5 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have bound := girth_five_min_degree_bound hg' (d := m+1) (by dsimp [m]; omega) minH a
  rw [if_pos ha] at bound
  have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  dsimp [m] at bound
  omega

/-- A lower bound on minimum degree proves the radius-two inequality whenever
the floor of the average neighborhood independence is at most that bound. -/
theorem girth_five_radius_two_of_min_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (hg : 5 ≤ G.egirth) (hr : G.radius.toNat ≤ 2) {d : ℕ}
    (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (hfloor : ⌊l G⌋₊ ≤ d) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  let a : V := hc.nonempty.some
  have := girth_five_min_degree_bound hg hd hmin a
  omega

/-- The fourth floor band of the conjecture at radius two. -/
theorem girth_five_radius_two_floor_four [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (hg : 5 ≤ G.egirth) (hr : G.radius.toNat ≤ 2) (hk : ⌊l G⌋₊ = 4) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path := by
  let : Nonempty V := hc.nonempty
  have nonneg : 0 ≤ l G :=
    div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)
  have avg := sum_degree_ge_of_le_l (G := G) (k := ⌊l G⌋₊) (Nat.floor_le nonneg)
  rw [hk] at avg
  have := girth_five_density_bound hg (le_refl 4) avg
  omega

end Wall133
