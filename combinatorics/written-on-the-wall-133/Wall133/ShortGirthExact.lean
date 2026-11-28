module

public import Wall133.ShortGirthOptions
public import Wall133.CoreExterior

@[expose] public section
namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {n : ℕ}

theorem extend_two_or_reroute_at (P : Chain G n) (h4 : NoFourCycle G) (hc : G.Connected)
    {D d : ℕ} (hD : 2 ≤ D) (hl : D ≤ n)
    (geo : ∀ i ≤ D,G.dist (P.vertex 0) (P.vertex i)=i)
    (ht : n-D+3 ≤ d)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x≠y) (nxy : ¬G.Adj x y)
    (wide : d ≤ G.indepNeighborsCard x ∨ d+1 ≤ G.degree x) :
    n+3 ≤ G.path := by
  classical
  let R := grow P x hx
  obtain ⟨A⟩ := exists_contact_options R (by omega) h4 wide
  by_contra short
  have fail (w : A.points) : ¬Good R w.val := fun good => short (grow R w.val good).length_le
  have block (w : A.points) : ∃ i ≤ n, G.Adj w.val (P.vertex i) := by
    by_contra! hb
    apply fail w
    refine ⟨A.adj w w.property,A.fresh w w.property,?_⟩
    rintro (_|i) hi iz
    · contradiction
    · exact hb i (by omega)
  have possible (w : A.points) (i : ℕ) (hi : i ≤ n) (ha : G.Adj w.val (P.vertex i)) :
      2 ≤ i ∧ (i ≤ D → i ≤ 3) := by
    have lo := A.lower _ w.property (i+1) (by omega) (by omega) ha
    refine ⟨by omega,fun h => ?_⟩
    have he := hc.dist_triangle (u := P.vertex 0) (v := x) (w := P.vertex i)
    have hf := hc.dist_triangle (u := x) (v := w.val) (w := P.vertex i)
    rw [geo i h,dist_eq_one_iff_adj.mpr hx.1] at he
    rw [dist_eq_one_iff_adj.mpr (show G.Adj x w.val from A.adj _ w.property),
      dist_eq_one_iff_adj.mpr ha] at hf
    omega
  choose idx hi ha using block
  let k := n-D+2
  let code (i : ℕ) := if i≤D then i-2 else 2+(i-D-1)
  have bound (w : A.points) (i : ℕ) (hi : i ≤ n) (ha : G.Adj w.val (P.vertex i)) : code i < k := by
    obtain ⟨lo,up⟩ := possible w i hi ha
    dsimp [code,k]; split_ifs <;> omega
  have injSite (w z : A.points) (i j : ℕ) (hi : i ≤ n) (hj : j≤n)
      (hwi : G.Adj w.val (P.vertex i)) (hzj : G.Adj z.val (P.vertex j)) (e : code i=code j) : i=j := by
    obtain ⟨li,ui⟩ := possible w i hi hwi
    obtain ⟨lj,uj⟩ := possible z j hj hzj
    dsimp [code] at e
    split_ifs at e <;> omega
  have same (w z : A.points) (i : ℕ) (hi : i≤n)
      (hwi : G.Adj w.val (P.vertex i)) (hzi : G.Adj z.val (P.vertex i)) : w=z := by
    apply Subtype.ext
    exact h4 (hx.2.1 i hi) (A.adj _ w.property) hwi.symm (A.adj _ z.property) hzi.symm
  let f (w : A.points) : Fin k := ⟨code (idx w),bound w _ (hi w) (ha w)⟩
  have inj : Function.Injective f := by
    intro w z e
    have eq := injSite w z _ _ (hi w) (hi z) (ha w) (ha z) (congrArg Fin.val e)
    exact same w z _ (hi w) (ha w) (eq ▸ ha z)
  have surj : Function.Surjective f := by
    apply ((Fintype.bijective_iff_injective_and_card f).2 ⟨inj,?_⟩).2
    apply (Fintype.card_le_of_injective f inj).antisymm
    simp only [Fintype.card_fin,Fintype.card_coe]
    have sz := A.size
    dsimp [k]; omega
  let zero : Fin k := ⟨0,by dsimp [k]; omega⟩
  obtain ⟨b,hb⟩ := surj zero
  have site : idx b=2 := by
    have eq := congrArg Fin.val hb
    change code (idx b)=0 at eq
    have := (possible b _ (hi b) (ha b)).1
    dsimp [code] at eq; split_ifs at eq <;> omega
  have privateSite (i : ℕ) (hi' : i≤n) (adj : G.Adj b.val (P.vertex i)) : i=2 := by
    obtain ⟨w,hw⟩ := surj (⟨code i,bound b i hi' adj⟩ : Fin k)
    have eq := injSite w b _ i (hi w) hi' (ha w) adj (congrArg Fin.val hw)
    have wb := same w b i hi' (eq ▸ ha w) adj
    rw [wb,site] at eq
    exact eq.symm
  apply short
  exact independent_end_reroute P (by omega) h4 hx hy hxy nxy (A.adj _ b.property)
    (fun i hi' => A.fresh _ b.property (i+1) (by omega))
    (fun i hi' => ⟨privateSite i hi',fun e => e ▸ site ▸ ha b⟩)

/-- In a four-cycle-free graph, a geodesic of length at least two ending at
a vertex with d independent neighbors gives an induced path of order at least
its length plus d, if each vertex has d independent neighbors or degree above d. -/
theorem geodesic_add_neighborhood_threshold_le_path (h4 : NoFourCycle G) (hc : G.Connected)
    {d : ℕ} (hmin : ∀ x,d ≤ G.indepNeighborsCard x ∨ d+1 ≤ G.degree x) {a v : V} (q : G.Walk a v)
    (hv : d≤G.indepNeighborsCard v)
    (hq : q.length=G.dist a v) (hlen : 2 ≤ q.length) : q.length+d ≤ G.path := by
  have hq' : Chordless q := ⟨q.isPath_of_length_eq_dist hq,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩
  obtain ⟨u,p,t,_,hp,hl,hs,hb⟩ := exists_saturated Set.univ q hq' (Set.mem_univ _)
  have ctrl : GirthFiveSlotControl G (fun _ => d) := by
    intro u v p hp hn k code bound inj sat
    obtain ⟨W,hW,⟨hα,hdeg⟩,idx,hI,hp'⟩ := exists_stalled_contacts_at hc h4 hp hn sat
    have pos (w : W) : GirthFivePossible p (idx w) := ⟨(hp' w).1,(hp' w).2.1,(hp' w).2.2.2⟩
    let f (w : W) : Fin k := ⟨code (idx w),bound _ (pos w)⟩
    have fi : Function.Injective f := fun w z e => hI (inj _ _ (pos w) (pos z) (congrArg Fin.val e))
    have cnt : W.card ≤ k := by simpa using Fintype.card_le_of_injective f fi
    have := hmin u
    change d ≤ k+1
    omega
  obtain ⟨first,_⟩ := girth_five_first_growth q hq p hp hc ctrl
    (by omega) hl hs (le_refl d) (fun w => hb w (Set.mem_univ _))
  let P := (chainOfChordless p hp).reverse
  have pref (i) (hi : i≤q.length) : P.vertex i=q.getVert (q.length-i) := by
    change p.getVert (p.length-i) = _
    rw [show p.length-i=t+(q.length-i) by omega,hs]
  have geo (i) (hi : i≤q.length) : G.dist (P.vertex 0) (P.vertex i)=i := by
    rw [pref 0 (by omega),pref i hi]
    simpa [G.dist_comm (u := v),show q.length-(q.length-i)=i by omega] using
      dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (show q.length-i≤q.length by omega) le_rfl
  apply two_at_geodesic_end P h4 hc hlen (by omega) geo (by omega) (by simpa [pref 0 (by omega)] using hv)
  exact fun ht {x y} hx hy hxy nxy => extend_two_or_reroute_at P h4 hc hlen (by omega) geo ht hx hy hxy nxy (hmin x)

end Wall133
