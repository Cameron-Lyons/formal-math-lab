module

public import Wall133.ShortGirthReroute

@[expose] public section
namespace Wall133
open SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

/-- A set of mutually independent neighbors at the active end. Its elements
stay off the path, and every positive-index contact starts at index three. -/
structure ContactOptions (P : Chain G n) (d : ℕ) where
  points : Finset V
  size : d ≤ points.card+1
  adj : ∀ w ∈ points,G.Adj (P.vertex 0) w
  fresh : ∀ w ∈ points,∀ i ≤ n,w ≠ P.vertex i
  lower : ∀ w ∈ points,∀ i ≤ n,i≠0 → G.Adj w (P.vertex i) → 3 ≤ i

structure IndependentOptions (P : Chain G n) extends ContactOptions P (G.indepNeighborsCard (P.vertex 0)) where
  independent : G.IsIndepSet (points : Set V)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem contact_options_of_eligible (P : Chain G n) (hn : 2 ≤ n) (h4 : NoFourCycle G)
    {I : Finset V} (mem : ∀ {w}, w∈I → G.Adj (P.vertex 0) w ∧ w≠P.vertex 1 ∧ ¬G.Adj (P.vertex 1) w)
    {d : ℕ} (size : d ≤ I.card+1) : ∃ A : ContactOptions P d,A.points=I := by
  have p01 := (P.edges (Nat.zero_le _) (show 1 ≤ n by omega)).2 (Or.inl rfl)
  refine ⟨⟨I,size,fun w hw => (mem hw).1,?_,?_⟩,rfl⟩
  · intro w hw i hi eq
    have := (P.edges (Nat.zero_le _) hi).1 (eq ▸ (mem hw).1)
    exact (mem hw).2.1 ((show i=1 by omega) ▸ eq)
  · intro w hw i hi ip ha
    by_contra! lo
    rcases (show i=1 ∨ i=2 by omega) with rfl|rfl
    · exact (mem hw).2.2 ha.symm
    · have ne : P.vertex 0 ≠ P.vertex 2 := fun e => by have := P.inj (Nat.zero_le _) hi e; omega
      exact (mem hw).2.1 (h4 ne (mem hw).1 ha.symm p01 ((P.edges hi (by omega)).2 (Or.inr rfl)))

theorem exists_independent_options (P : Chain G n) (hn : 2 ≤ n) (h4 : NoFourCycle G) :
    Nonempty (IndependentOptions P) := by
  classical
  let W := (G.neighborFinset (P.vertex 0)).filter (fun w => w≠P.vertex 1 ∧ ¬G.Adj (P.vertex 1) w)
  have wmem (w) : w∈W ↔ G.Adj (P.vertex 0) w ∧ w≠P.vertex 1 ∧ ¬G.Adj (P.vertex 1) w := by simp [W]
  have p01 := (P.edges (Nat.zero_le _) (show 1 ≤ n by omega)).2 (Or.inl rfl)
  obtain ⟨⟨I,sub,ind,size⟩,_⟩ := eligible_neighbors_data h4 p01 W wmem
  have mem {w} (hw : w∈I) := (wmem w).1 (sub hw)
  obtain ⟨A,hA⟩ := contact_options_of_eligible P hn h4 mem size
  exact ⟨⟨A,hA ▸ ind⟩⟩

theorem exists_contact_options (P : Chain G n) (hn : 2 ≤ n) (h4 : NoFourCycle G) {d : ℕ}
    (h : d≤G.indepNeighborsCard (P.vertex 0) ∨ d+1≤G.degree (P.vertex 0)) :
    Nonempty (ContactOptions P d) := by
  classical
  let W := (G.neighborFinset (P.vertex 0)).filter (fun w => w≠P.vertex 1 ∧ ¬G.Adj (P.vertex 1) w)
  have wmem (w) : w∈W ↔ G.Adj (P.vertex 0) w ∧ w≠P.vertex 1 ∧ ¬G.Adj (P.vertex 1) w := by simp [W]
  have p01 := (P.edges (Nat.zero_le _) (show 1 ≤ n by omega)).2 (Or.inl rfl)
  obtain ⟨alpha,deg⟩ := eligible_neighbors_card h4 p01 W wmem
  obtain ⟨A,_⟩ := contact_options_of_eligible P hn h4 (fun {w} hw => (wmem w).1 hw) (by omega : d ≤ W.card+1)
  exact ⟨A⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem same_neighbor (P : Chain G n) (h4 : NoFourCycle G) {i : ℕ} (hi : i≤n) (ip : i≠0)
    {w z : V} (hw : G.Adj (P.vertex 0) w) (hz : G.Adj (P.vertex 0) z)
    (hwi : G.Adj w (P.vertex i)) (hzi : G.Adj z (P.vertex i)) : w=z :=
  h4 (fun e => ip (P.inj (Nat.zero_le _) hi e).symm) hw hwi.symm hz hzi.symm

omit [Fintype V] [DecidableEq V] in
theorem options_good_count (P : Chain G n) (h4 : NoFourCycle G)
    (A : IndependentOptions P) {D : ℕ}
    (far : ∀ w∈A.points, ∀ i≤n,i≠0 → G.Adj w (P.vertex i) → D < i) :
    A.points.card ≤ (A.points.filter (Good P)).card + (n-D) := by
  classical
  let B := A.points.filter (fun x => ¬Good P x)
  have mem (u : B) := (Finset.mem_filter.mp u.property).1
  have block (u : B) : ∃ i ≤ n,i≠0 ∧ G.Adj u.val (P.vertex i) := by
    by_contra! h
    exact (Finset.mem_filter.mp u.property).2 ⟨A.adj _ (mem u),A.fresh _ (mem u),h⟩
  choose idx hi hp hadj using block
  let f (u : B) : Fin (n-D) := ⟨idx u-D-1,by have := far _ (mem u) _ (hi u) (hp u) (hadj u); have := hi u; omega⟩
  have inj : Function.Injective f := by
    intro u v he
    have e := congrArg Fin.val he
    change idx u-D-1=idx v-D-1 at e
    have eq : idx u=idx v := by
      have := far _ (mem u) _ (hi u) (hp u) (hadj u)
      have := far _ (mem v) _ (hi v) (hp v) (hadj v)
      omega
    exact Subtype.ext (same_neighbor P h4 (hi u) (hp u) (A.adj _ (mem u)) (A.adj _ (mem v))
      (hadj u) (eq ▸ hadj v))
  have bound : B.card ≤ n-D := by simpa using Fintype.card_le_of_injective f inj
  have cnt := Finset.card_filter_add_card_filter_not (s := A.points) (Good P)
  change (A.points.filter (Good P)).card+B.card = A.points.card at cnt
  omega

theorem two_at_geodesic_end (P : Chain G n) (hg : NoFourCycle G) (hc : G.Connected)
    {D d : ℕ} (hD : 2≤D) (hlen : D≤n)
    (suf : ∀ i ≤ D,G.dist (P.vertex 0) (P.vertex i)=i)
    (first : d ≤ n-D+3) (hroot : d≤G.indepNeighborsCard (P.vertex 0))
    (deep : n-D+3 ≤ d → ∀ {x y : V}, Good P x → Good P y → x≠y → ¬G.Adj x y → n+3≤G.path) :
    D+d ≤ G.path := by
  classical
  by_contra! short
  have base := P.length_le
  obtain ⟨A⟩ := exists_independent_options P (by omega) hg
  have cnt := options_good_count P hg A (D := D) (by
    intro w hw i hi ip ha
    by_contra! early
    have ln := A.lower w hw i hi ip ha
    have dd := hc.dist_triangle (u := P.vertex 0) (v := w) (w := P.vertex i)
    rw [suf i early,dist_eq_one_iff_adj.mpr (A.adj w hw),dist_eq_one_iff_adj.mpr ha] at dd
    omega)
  have hc₁ := A.size
  let good := A.points.filter (Good P)
  have extract {w : V} (hw : w ∈ good) := Finset.mem_filter.mp hw
  change A.points.card ≤ good.card+(n-D) at cnt
  by_cases hlarge : n+2 ≤ G.path
  · have many : 1 < good.card := by omega
    obtain ⟨x,y,hx,hy,hxy⟩ := Finset.one_lt_card_iff.mp many
    have xy := A.independent (extract hx).1 (extract hy).1 hxy
    have := deep (by omega) (extract hx).2 (extract hy).2 hxy xy
    omega
  · have one : 0 < good.card := by omega
    obtain ⟨x,hx⟩ := Finset.card_pos.mp one
    exact hlarge (grow P x (extract hx).2).length_le

end Wall133
