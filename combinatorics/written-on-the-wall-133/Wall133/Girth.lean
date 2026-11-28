module

public import Wall133.Density
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

/-!
# The girth-seven case

Peeling vertices of low degree yields an induced subgraph of minimum degree
at least `k / 2 + 1`, where `k` is the floor of the average degree. Start a
geodesic of length at least the radius at a vertex of this subgraph and extend
the path there, staying in the subgraph. At a saturated endpoint, each unused
neighbor must have a second neighbor on the path. Girth seven forces the
indices of these attachment points to start at five and be at least three
apart. At most two occur on the original geodesic, because their distances
from its far endpoint differ by at most four. Counting the rest gives
`radius + 3 * d ≤ path + 5` for minimum core degree `d ≥ 4`.

For smaller `k`, the same spacing argument gives a long path in the core;
Chung's bound handles large radius.
-/

namespace Wall133

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {u v : V} {g : ℕ}

private lemma paths_equal_when_short (hg : (g : ℕ∞) ≤ G.egirth)
    {a b : V} {p q : G.Walk a b} (hp : p.IsPath) (hq : q.IsPath)
    (hlen : p.length + q.length < g) : p = q := by
  by_contra h
  obtain ⟨w, _, _, c, hc, hlen'⟩ := hp.exists_isCycle_length_le_add_of_ne hq h
  have h := hg.trans hc.egirth_le_length
  have : g ≤ c.length := ENat.natCast_le_natCast.mp h
  omega

/-- A chordless walk, indexed from the end where it can be extended. -/
structure Chordless (p : G.Walk u v) : Prop where
  simple : p.IsPath
  consecutive : ∀ i j, i ≤ p.length → j ≤ p.length →
    G.Adj (p.getVert i) (p.getVert j) → i+1 = j ∨ j+1 = i

lemma Chordless.extend {p : G.Walk u v} (hp : Chordless p)
    {w : V} (huw : G.Adj u w) (hnew : w ∉ p.support)
    (hclean : ∀ i ≤ p.length, i ≠ 0 → ¬ G.Adj w (p.getVert i)) :
    Chordless (p.cons huw.symm) := by
  refine ⟨hp.simple.cons hnew, ?_⟩
  intro i j hi hj ha
  cases i <;> cases j
  · exact (ha.ne rfl).elim
  · rename_i j
    by_cases h : j = 0
    · omega
    · exact (hclean j (by simpa using hj) h ha).elim
  · rename_i i
    by_cases h : i = 0
    · omega
    · exact (hclean i (by simpa using hi) h ha.symm).elim
  · rename_i i j
    have := hp.consecutive i j (by simpa using hi) (by simpa using hj) ha
    omega

lemma Chordless.pending_off_path {p : G.Walk u v} (hp : Chordless p)
    {w : V} (hw : G.Adj u w) (hne : w ≠ p.getVert 1) : w ∉ p.support := by
  intro h
  obtain ⟨j, hjw, hj⟩ := Walk.mem_support_iff_exists_getVert.mp h
  have ha : G.Adj (p.getVert 0) (p.getVert j) := by simpa [hjw] using hw
  have := hp.consecutive 0 j (Nat.zero_le _) hj ha
  exact hne ((show j = 1 by omega) ▸ hjw.symm)

/-- A neighbor off the path can only meet it again at distance at least girth minus two. -/
lemma first_blocker {p : G.Walk u v} (hg : (g : ℕ∞) ≤ G.egirth)
    (hp : Chordless p) {w : V} (hw : G.Adj u w) (hoff : w ∉ p.support)
    {j : ℕ} (hj : j ≤ p.length) (hpos : j ≠ 0) (hblock : G.Adj w (p.getVert j)) :
    g ≤ j+2 := by
  have hv : u ≠ p.getVert j := by
    intro h
    have := hp.simple.getVert_injOn (x₁ := 0) (x₂ := j) (Nat.zero_le _) hj (by simpa using h)
    omega
  let q : G.Walk u (p.getVert j) := .cons hw (.cons hblock .nil)
  have hq : q.IsPath := by simp [q, Walk.isPath_def, hw.ne, hblock.ne, hv]
  by_contra! h
  have he := paths_equal_when_short hg (hp.simple.take j) hq (by simpa [q, Nat.min_eq_left hj] using h)
  have hm : w ∈ (p.take j).support := by rw [he]; simp [q]
  exact hoff ((Walk.isSubwalk_iff_support_isInfix.mp (Walk.isSubwalk_take p j)).sublist.subset hm)

/-- Two different neighbors off the path have attachment indices separated by girth minus four. -/
lemma separated_blockers {p : G.Walk u v} (hg : (g : ℕ∞) ≤ G.egirth)
    (hp : Chordless p) {w z : V} (hw : G.Adj u w) (hz : G.Adj u z)
    (hwoff : w ∉ p.support) (hzoff : z ∉ p.support) (hwz : w ≠ z)
    {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) (hj : j ≤ p.length)
    (hwi : G.Adj w (p.getVert i)) (hzj : G.Adj z (p.getVert j))
    (hg4 : 4 < g) : g ≤ 4 + (j-i) := by
  by_contra! hshort
  have hu (a : ℕ) (ha : 0 < a) (halen : a ≤ p.length) : u ≠ p.getVert a := by
    intro h
    have := hp.simple.getVert_injOn (x₁ := 0) (x₂ := a) (Nat.zero_le _) halen (by simpa using h)
    omega
  by_cases hEq : i = j
  · subst j
    let q : G.Walk u (p.getVert i) := .cons hw (.cons hwi .nil)
    let s : G.Walk u (p.getVert i) := .cons hz (.cons hzj .nil)
    have hq : q.IsPath := by simp [q, Walk.isPath_def, hw.ne, hwi.ne, hu i hi hj]
    have hs : s.IsPath := by simp [s, Walk.isPath_def, hz.ne, hzj.ne, hu i hi hj]
    have he := paths_equal_when_short hg hq hs (by simpa [q,s] using hg4)
    exact (hwz (congrArg (fun (r : G.Walk u (p.getVert i)) => r.getVert 1) he)).elim
  have hneq : p.getVert i ≠ p.getVert j :=
    fun h => hEq (hp.simple.getVert_injOn (hij.trans hj) hj h)
  have hwj : p.getVert j ≠ w := fun he => hwoff (he ▸ p.getVert_mem_support j)
  have hzi : p.getVert i ≠ z := fun he => hzoff (he ▸ p.getVert_mem_support i)
  let q : G.Walk (p.getVert i) (p.getVert j) := .cons hwi.symm (.cons hw.symm (.cons hz (.cons hzj .nil)))
  have hq : q.IsPath := by
    simp [q, Walk.isPath_def, hwi.ne.symm, hzj.ne, hw.ne.symm, hz.ne,
      (hu i hi (hij.trans hj)).symm, hu j (hi.trans_le hij) hj, hneq, hwj.symm, hzi, hwz]
  have hend : (p.drop i).getVert (j-i) = p.getVert j := by simp [Nat.add_sub_of_le hij]
  let s := ((p.drop i).take (j-i)).copy rfl hend
  have hs : s.IsPath := by simpa [s] using (hp.simple.drop i).take (j-i)
  have hlen : s.length = j-i := by simp only [s, Walk.length_copy, Walk.take_length, Walk.drop_length]; omega
  have he := paths_equal_when_short hg hq hs (by simpa [q, hlen] using hshort)
  have hm : w ∈ s.support := by rw [← he]; simp [q]
  have hsub := (Walk.isSubwalk_take (p.drop i) (j-i)).trans (Walk.isSubwalk_drop p i)
  apply hwoff
  exact (Walk.isSubwalk_iff_support_isInfix.mp hsub).sublist.subset (by simpa [s] using hm)

/-- A longest induced walk starting at some endpoint among the permitted vertices.
The initial walk can be used to prescribe a geodesic at its far end. -/
lemma exists_saturated_inside [Fintype V] [DecidableEq V] {v a : V}
    (S : Set V) (p₀ : G.Walk a v) (h₀ : Chordless p₀) (ha : a ∈ S) :
    ∃ (u : V) (p : G.Walk u v) (t : ℕ),
      u ∈ S ∧ Chordless p ∧ p.length = t + p₀.length ∧
      (∀ j, p.getVert (t+j) = p₀.getVert j) ∧
      (∀ i < t, p.getVert i ∈ S) ∧
      (∀ w ∈ S, G.Adj u w → w ∉ p.support →
        ∃ i, i ≤ p.length ∧ i ≠ 0 ∧ G.Adj w (p.getVert i)) := by
  classical
  let P (n : ℕ) := ∃ (u : V) (p : G.Walk u v) (t : ℕ),
    u ∈ S ∧ Chordless p ∧ n = p.length ∧ p.length = t + p₀.length ∧
      (∀ j, p.getVert (t+j) = p₀.getVert j) ∧ ∀ i < t, p.getVert i ∈ S
  have h₀' : P p₀.length := ⟨a, p₀, 0, ha, h₀, rfl, by simp, by simp, by simp⟩
  let lengths := (Finset.range (Fintype.card V)).filter P
  have hmem {n} (hn : P n) : n ∈ lengths := by
    refine Finset.mem_filter.mpr ⟨?_, hn⟩
    obtain ⟨u, p, t, _, hp, rfl, _, _⟩ := hn
    exact Finset.mem_range.mpr hp.simple.length_lt
  obtain ⟨n, hn, hmax⟩ := Finset.exists_max_image lengths id ⟨_, hmem h₀'⟩
  obtain ⟨u, p, t, hu, hp, hn', hlen, hsuf, hpre⟩ := (Finset.mem_filter.mp hn).2
  refine ⟨u,p,t,hu,hp,hlen,hsuf,hpre,?_⟩
  intro w hw hadj hoff
  by_contra! hclean
  have hext : P (p.length+1) := by
    refine ⟨w, p.cons hadj.symm, t+1, hw, hp.extend hadj hoff hclean, rfl, ?_, ?_, ?_⟩
    · simp [hlen, Nat.add_right_comm]
    · intro j
      rw [show t+1+j = (t+j)+1 by omega, Walk.getVert_cons_succ, hsuf]
    · intro i hi
      cases i with
      | zero => simpa using hw
      | succ i => simpa using hpre i (by omega)
  have := hmax _ (hmem hext)
  change p.length+1 ≤ n at this
  omega

lemma exists_saturated [Fintype V] [DecidableEq V] {v a : V}
    (S : Set V) (p₀ : G.Walk a v) (h₀ : Chordless p₀) (ha : a ∈ S) :
    ∃ (u : V) (p : G.Walk u v) (t : ℕ),
      u ∈ S ∧ Chordless p ∧ p.length = t + p₀.length ∧
      (∀ j, p.getVert (t+j) = p₀.getVert j) ∧
      (∀ w ∈ S, G.Adj u w → w ∉ p.support →
        ∃ i, i ≤ p.length ∧ i ≠ 0 ∧ G.Adj w (p.getVert i)) := by
  obtain ⟨u,p,t,hu,hp,hl,hs,_,hb⟩ := exists_saturated_inside S p₀ h₀ ha
  exact ⟨u,p,t,hu,hp,hl,hs,hb⟩

private structure AttachmentIndices (W : Finset V) (n : ℕ) where
  index : W → ℕ
  lower : ∀ w, 5 ≤ index w
  upper : ∀ w, index w ≤ n
  gap : ∀ w z, w ≠ z → index w ≤ index z → index w + 3 ≤ index z

private noncomputable def attachmentIndices [DecidableEq V] {p : G.Walk u v}
    (hg : 7 ≤ G.egirth) (hp : Chordless p) (W : Finset V)
    (hW : ∀ w ∈ W, G.Adj u w ∧ w ≠ p.getVert 1)
    (hblock : ∀ w ∈ W, ∃ i, i ≤ p.length ∧ i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    {I : AttachmentIndices W p.length // ∀ w, G.Adj w.val (p.getVert (I.index w))} := by
  classical
  choose idx hidx using (fun (w : W) => hblock w.val w.property)
  have info (w : W) := hW w.val w.property
  have hoff (w : W) := hp.pending_off_path (info w).1 (info w).2
  have hlo (w : W) : 5 ≤ idx w := by
    have := first_blocker (g := 7) hg hp (info w).1 (hoff w) (hidx w).1 (hidx w).2.1 (hidx w).2.2
    omega
  have hgap (w z : W) (h : w ≠ z) (hij : idx w ≤ idx z) : idx w + 3 ≤ idx z := by
    have := separated_blockers (g := 7) hg hp (info w).1 (info z).1 (hoff w) (hoff z)
      (fun he => h (Subtype.ext he)) (by have := hlo w; omega) hij (hidx z).1
      (hidx w).2.2 (hidx z).2.2 (by decide)
    omega
  exact ⟨⟨idx, hlo, fun w => (hidx w).1, hgap⟩, fun w => (hidx w).2.2⟩

private lemma AttachmentIndices.card_bound {W : Finset V} {n : ℕ} (I : AttachmentIndices W n) :
    W.card ≤ (n-2)/3 := by
  let f (w : W) : Fin ((n-2)/3) := ⟨(I.index w-5)/3, by have := I.lower w; have := I.upper w; omega⟩
  have inj : Function.Injective f := by
    intro w z he
    by_contra h
    have eq := congrArg Fin.val he
    change (I.index w-5)/3 = (I.index z-5)/3 at eq
    have := I.lower w
    have := I.lower z
    rcases le_total (I.index w) (I.index z) with hle | hle
    · have := I.gap w z h hle
      omega
    · have := I.gap z w (Ne.symm h) hle
      omega
  simpa using Fintype.card_le_of_injective f inj

private lemma saturated_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {p : G.Walk u v} (hg : 7 ≤ G.egirth) (hp : Chordless p)
    (hblock : ∀ w, G.Adj u w → w ∉ p.support →
      ∃ i, i ≤ p.length ∧ i ≠ 0 ∧ G.Adj w (p.getVert i)) :
    G.degree u - 1 ≤ (p.length-2)/3 := by
  classical
  let W := (G.neighborFinset u).erase (p.getVert 1)
  have hW (w : V) (hw : w ∈ W) : G.Adj u w ∧ w ≠ p.getVert 1 :=
    ⟨(G.mem_neighborFinset _ _).mp (Finset.mem_erase.mp hw).2, (Finset.mem_erase.mp hw).1⟩
  let I := attachmentIndices hg hp W hW (fun w hw => hblock w (hW w hw).1
    (hp.pending_off_path (hW w hw).1 (hW w hw).2))
  exact (show G.degree u - 1 ≤ W.card from Finset.pred_card_le_card_erase).trans I.val.card_bound

lemma Chordless.reverse {p : G.Walk u v} (hp : Chordless p) : Chordless p.reverse := by
  refine ⟨hp.simple.reverse, ?_⟩
  intro i j hi hj ha
  simp only [Walk.length_reverse] at hi hj
  simp only [Walk.getVert_reverse] at ha
  have := hp.consecutive _ _ (Nat.sub_le _ _) (Nat.sub_le _ _) ha
  omega

/-- At girth at least seven, a minimum degree of d gives an induced path on
3d vertices. Starting at a vertex of higher degree gains one further vertex. -/
theorem girth_seven_min_degree_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hg : 7 ≤ G.egirth) {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x, d ≤ G.degree x)
    (a : V) : 3*d + (if d < G.degree a then 1 else 0) ≤ G.path := by
  classical
  let start : G.Walk a a := .nil
  have hstart : Chordless start := ⟨Walk.IsPath.nil, by simp [start]⟩
  obtain ⟨u,p,_,_,hp,_,_,hb⟩ := exists_saturated Set.univ start hstart (Set.mem_univ a)
  have hdeg := saturated_degree hg hp (fun w => hb w (Set.mem_univ _))
  have hmu := hmin u
  obtain ⟨z,q,t,_,hq,hlen,hsuf,hb'⟩ := exists_saturated Set.univ p.reverse hp.reverse (Set.mem_univ a)
  have hlen' : q.length = t + p.length := by simpa using hlen
  have hl := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert q
    hq.simple hq.consecutive)
  rw [Walk.length_support] at hl
  split_ifs with hhi
  · by_cases ht : t = 0
    · subst t
      have hza : z = a := by simpa using hsuf 0
      have hdeg' := saturated_degree hg hq (fun w => hb' w (Set.mem_univ _))
      have : G.degree z = G.degree a := by subst z; rfl
      omega
    · omega
  · omega

/-- Separate attachments on the extension from those meeting the original geodesic.
On a geodesic, all attachment indices lie in an interval of width four. -/
private lemma AttachmentIndices.geodesic_bound {W : Finset V} {n t b : ℕ}
    (I : AttachmentIndices W n) (hsuf : ∀ w, t ≤ I.index w →
      b ≤ I.index w ∧ I.index w ≤ b+4) :
    W.card ≤ (t-3)/3 + 2 := by
  let code (w : W) := if I.index w < t then (I.index w-5)/3
    else (t-3)/3 + (I.index w-b)/3
  let f (w : W) : Fin ((t-3)/3+2) := ⟨code w, by
    dsimp [code]
    split_ifs with h
    · have := I.lower w; omega
    · have := hsuf w (by omega); omega⟩
  have inj : Function.Injective f := by
    intro w z he
    by_contra hne
    have eq := congrArg Fin.val he
    change code w = code z at eq
    have := I.lower w
    have := I.lower z
    have gap : I.index w + 3 ≤ I.index z ∨ I.index z + 3 ≤ I.index w := by
      rcases le_total (I.index w) (I.index z) with h | h
      · exact Or.inl (I.gap w z hne h)
      · exact Or.inr (I.gap z w (Ne.symm hne) h)
    dsimp [code] at eq
    split_ifs at eq with hw hz hz <;> first | omega | (have := hsuf w (by omega); have := hsuf z (by omega); omega)
  simpa using Fintype.card_le_of_injective f inj

/-- Extend a geodesic from a vertex in the core. Only two pending neighbors can
attach to its original geodesic segment, regardless of the radius. -/
theorem girth_seven_radius_core_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hg : 7 ≤ G.egirth) (hc : G.Connected) (S : Finset V) (hS : S.Nonempty)
    {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ x : S, d ≤ (G.induce (S : Set V)).degree x) :
    G.radius.toNat + 3*d ≤ G.path + 5 := by
  classical
  obtain ⟨a, ha⟩ := hS
  obtain ⟨v,q,hq,hr⟩ := exists_geodesic_ge_radius G hc a
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,hu,hp,hlen,hsuf,hb⟩ := exists_saturated (S : Set V) q hq' ha
  let H := G.induce (S : Set V)
  let uS : S := ⟨u,hu⟩
  let A := (H.neighborFinset uS).map (Function.Embedding.subtype (· ∈ S))
  let W := A.erase (p.getVert 1)
  have hW (w : V) (hw : w ∈ W) : G.Adj u w ∧ w ≠ p.getVert 1 ∧ w ∈ S := by
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hw
    obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hmem
    exact ⟨(H.mem_neighborFinset _ _).mp hw', hne, w'.property⟩
  obtain ⟨I, hI⟩ := attachmentIndices hg hp W (fun w hw => ⟨(hW w hw).1, (hW w hw).2.1⟩)
    (fun w hw => hb w (hW w hw).2.2 (hW w hw).1 (hp.pending_off_path (hW w hw).1 (hW w hw).2.1))
  let b := p.length - (G.dist u v + 2)
  have win (w : W) (hi : t ≤ I.index w) : b ≤ I.index w ∧ I.index w ≤ b+4 := by
    let j := I.index w - t
    have hj : j ≤ q.length := by have := I.upper w; dsimp [j]; omega
    have hj' : t+j = I.index w := Nat.add_sub_of_le hi
    have he : p.getVert (I.index w) = q.getVert j := hj' ▸ hsuf j
    have hdist : G.dist (p.getVert (I.index w)) v = q.length-j := by
      rw [he]
      simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq hj le_rfl
    have hnear : G.dist u (p.getVert (I.index w)) ≤ 2 :=
      (hc.dist_triangle (u := u) (v := (w : V)) (w := p.getVert (I.index w))).trans_eq
        (by rw [dist_eq_one_iff_adj.mpr (hW w w.property).1, dist_eq_one_iff_adj.mpr (hI w)])
    have h1 : G.dist u v ≤ G.dist u (p.getVert (I.index w)) + G.dist (p.getVert (I.index w)) v :=
      hc.dist_triangle
    have h2 : G.dist (p.getVert (I.index w)) v ≤ G.dist u (p.getVert (I.index w)) + G.dist u v :=
      by simpa only [G.dist_comm (u := p.getVert (I.index w)) (v := u)] using (hc.dist_triangle (u := p.getVert (I.index w)) (v := u) (w := v))
    dsimp [b]
    omega
  have hcard := I.geodesic_bound win
  have hsize : A.card = H.degree uS := by simp [A]
  have hrem : A.card - 1 ≤ W.card := Finset.pred_card_le_card_erase
  have hdeg : d ≤ H.degree uS := hmin uS
  have hl := G.length_le_path_of_isInducedPath _ (isInducedPath_support_of_isPath_of_adj_getVert p
    hp.simple hp.consecutive)
  rw [Walk.length_support] at hl
  omega

/-- WOWII 133 for graphs of extended girth at least seven, including forests.
The floor of the average degree can replace the floor of the neighborhood
independence average in this bound. -/
theorem radius_add_le_path_of_girth_seven_density [Fintype V] [DecidableEq V]
    [Nonempty V] [DecidableRel G.Adj] (hg : 7 ≤ G.egirth) (hc : G.Connected)
    {k : ℕ} (hav : k * Fintype.card V ≤ ∑ v, G.degree v) :
    G.radius.toNat + k ≤ G.path := by
  classical
  by_cases hk : k ≤ 1
  · have := radius_add_one_le_path G hc
    omega
  by_cases hlarge : 6 ≤ k
  · obtain ⟨S,hS,hcore⟩ := exists_degree_core G (by omega) hav
    have := girth_seven_radius_core_bound hg hc S hS (by omega : 4 ≤ k/2+1) hcore
    omega
  -- For the remaining degrees, the path through the core suffices on its own.
  have htarget (h : 2*k ≤ G.path) : G.radius.toNat + k ≤ G.path := by
    have := chung_bound_nat G hc
    omega
  apply htarget
  let m := k/2
  have hcost : 2 * (∑ _ : V, m) ≤ ∑ x, G.degree x := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ = (2*m)*Fintype.card V := by ac_rfl
      _ ≤ k*Fintype.card V := Nat.mul_le_mul_right _ (by dsimp [m]; omega)
      _ ≤ _ := hav
  obtain ⟨S,hS,hmin,hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by dsimp [m]; omega) hcost
  let H := G.induce (S : Set V)
  have : Nonempty S := hS.to_subtype
  have hg' : 7 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have hmono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  have hregular (v : S) : m+1 ≤ H.degree v := hmin v
  by_cases hf : k = 5
  · have hm : m = 2 := by simp [m,hf]
    have h₄ : ∃ x : S, 3 < H.degree x := by
      by_contra! h
      have hle := Finset.sum_le_sum (s := Finset.univ) (fun (x : S) _ => h x)
      have hp := Fintype.card_pos (α := S)
      change 2*(∑ _x ∈ S, m) ≤ ∑ v : S, H.degree v at hsum
      simp only [hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe] at hsum hle hp
      change 2 * (S.card * 2) ≤ ∑ x : S, H.degree x at hsum
      change (∑ x : S, H.degree x) ≤ S.card * 3 at hle
      omega
    obtain ⟨a, ha⟩ := h₄
    have h := girth_seven_min_degree_bound hg' (d := m+1) (by omega) hregular a
    rw [ite_eq_left (by omega : m+1 < H.degree a)] at h
    omega
  · obtain ⟨a⟩ := ‹Nonempty S›
    have h := girth_seven_min_degree_bound hg' (d := m+1) (by dsimp [m]; omega) hregular a
    dsimp [m] at h
    omega

theorem radius_add_floor_le_path_of_girth_seven [Fintype V] [DecidableEq V]
    [Nonempty V] [DecidableRel G.Adj] (hg : 7 ≤ G.egirth) (hc : G.Connected) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  apply radius_add_le_path_of_girth_seven_density hg hc
  apply sum_degree_ge_of_le_l (G := G)
  apply Nat.floor_le
  exact div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)

end Wall133
