import Wall133.OddRadiusSeven

namespace Wall133
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A pair of external neighbors accounts for two disjoint pairs among
the four nonprivate sites in a stalled second extension at degree six. -/
structure SixProfile (P : Chain G 14) (z : V) where
  support : Fin 2 → Finset (Fin 4)
  point : Fin 2 → V
  edges : ∀ i, G.Adj z (point i)
  off : ∀ i, Off P (point i) (fun k => ∃ j ∈ support i, k=4*j.val+2)
  distinct : point 0 ≠ point 1
  disjoint : Disjoint (support 0) (support 1)
  two : ∀ i, 2 ≤ (support i).card
  privateSite : ∀ (j : Fin 3), ∃ u, G.Adj z u ∧ Off P u (· = 4*j.val+4)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
private theorem compressed_bad_sites :
    ∀ E : Finset (Fin 8), E.card ≤ 4 → 1 ∈ E → 7 ∈ E →
      (∀ j k : Fin 8, 1 ≤ j.val → k.val = j.val+1 → j ∈ E ∨ k ∈ E) →
      E = {1,3,5,7} := by decide

set_option maxHeartbeats 600000 in
theorem six_profile_of_short (P : Chain G 14) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {x y z : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (hd : 6 ≤ G.degree z) (short : ¬18 ≤ G.path) :
    Nonempty (SixProfile P z) := by
  classical
  let Q := grow (grow P x hx) z hz
  have sat (w : V) : ¬ Good Q w := fun hw => short (grow Q w hw).length_le
  obtain ⟨B,hB,priv⟩ := private_contact_exceptions Q c h4 (by decide) (s := 2)
    (by change 8 ≤ G.degree z+2; omega) sat
  let E := (Finset.univ : Finset (Fin 8)).filter fun i => ¬PrivateContact Q i
  have memE {i : Fin 8} : i ∈ E ↔ ¬PrivateContact Q i := by simp [E]
  have hEc : E.card ≤ 4 :=
    (Finset.card_le_card (show E ⊆ B from fun i hi => by by_contra hh; exact (memE.mp hi) (priv i hh))).trans hB
  have witness (i : Fin 8) (hi : 1 ≤ i.val) (hp : PrivateContact Q i) :
      ∃ b, G.Adj z b ∧ Off P b (· = 2*i.val) :=
    contactOnSuffix P Q (r := 2) (by decide) (by omega) (by have := i.isLt; omega)
      (by decide) (fun _ _ => rfl)
      (fun j hj h => False.elim (hz.2.2 (j+1) (by omega) (by omega) h)) i rfl hp
  have extreme (i : Fin 8) (hi : 1 ≤ i.val) (hei : 2*i.val=2 ∨ 2*i.val=14) : i ∈ E := by
    apply memE.mpr
    intro hp
    obtain ⟨u,hzu,hp⟩ := witness i hi hp
    exact short (path_of_private_end P c h4 (by decide) hx hy hxy hz hzu _ hei hp.fresh hp.contact)
  have eE := compressed_bad_sites E hEc (extreme 1 (by decide) (Or.inl rfl))
    (extreme 7 (by decide) (Or.inr rfl)) (fun j k hj he => by
      by_contra! h
      have pj : PrivateContact Q j := by by_contra hp; exact h.1 (memE.mpr hp)
      have pk : PrivateContact Q k := by by_contra hp; exact h.2 (memE.mpr hp)
      exact short (path_of_two_step_pair P c h4 hx hy hxy hz _ _ hj he pj pk))
  let idx (j : Fin 4) : Fin 8 := ⟨2*j.val+1,by have := j.isLt; omega⟩
  have bad (j : Fin 4) : ¬PrivateContact Q (idx j) := by
    apply memE.mp; rw [eE]; fin_cases j <;> simp [idx,Fin.ext_iff]
  have outside {i : Fin 8} (hi : i.val%2=0) : PrivateContact Q i := by
    by_contra no
    have he := memE.mpr no
    rw [eE] at he
    fin_cases i <;> simp_all
  let N := G.neighborFinset z
  let hits (w : V) := (Finset.univ : Finset (Fin 4)).filter fun j => G.Adj (P.vertex (4*j.val+2)) w
  have hit {w : V} {j : Fin 4} : j ∈ hits w ↔ G.Adj (P.vertex (4*j.val+2)) w := by simp [hits]
  have idQ (j : Fin 4) : Q.vertex (2*(idx j).val+2) = P.vertex (4*j.val+2) := by
    rw [show 2*(idx j).val+2 = (4*j.val+2)+2 by dsimp [idx]; omega]
    rfl
  have idP (i : Fin 8) : Q.vertex (2*i.val+2) = P.vertex (2*i.val) := rfl
  let W := N.filter (fun w => (hits w).Nonempty)
  let L := N.filter (fun w => ¬(hits w).Nonempty)
  have lh : L.card ≤ 4 := by
    have site (w : L) : ∃ k : Fin 8, G.Adj (P.vertex (2*k.val)) w.val := by
      have ha := (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp w.property).1
      obtain ⟨k,hk⟩ := blocker Q c (by decide) ha (sat w.val)
      exact ⟨k,hk⟩
    choose f hf using site
    have even (w : L) : (f w).val % 2 = 0 := by
      by_contra he
      let j : Fin 4 := ⟨(f w).val/2,by have := (f w).isLt; omega⟩
      have eq : 2*(f w).val = 4*j.val+2 := by dsimp [j]; omega
      exact (Finset.mem_filter.mp w.property).2 ⟨j,hit.mpr (eq ▸ hf w)⟩
    let g (w : L) : Fin 4 := ⟨(f w).val/2,by have := (f w).isLt; omega⟩
    have inj : Function.Injective g := by
      intro u w e
      have eq := congrArg Fin.val e
      change (f u).val/2 = (f w).val/2 at eq
      have fk : f u = f w := Fin.ext (by have := even u; have := even w; omega)
      apply Subtype.ext
      apply unique_at_site Q h4 (f u)
      · exact (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp u.property).1
      · exact hf u
      · exact (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp w.property).1
      · exact fk.symm ▸ hf w
    simpa using Fintype.card_le_of_injective g inj
  have counts := Finset.card_filter_add_card_filter_not (s := N) (fun w => (hits w).Nonempty)
  change W.card+L.card = G.degree z at counts
  obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < W.card)
  have adj {u : V} (hu : u ∈ W) : G.Adj z u :=
    (G.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hu).1
  have other {u : V} (hu : u ∈ W) {k : Fin 8} (hk : G.Adj (Q.vertex (2*k.val+2)) u) :
      k.val%2 = 1 := by
    by_contra hh
    obtain ⟨w,hw,hwk,only⟩ := outside (by omega : k.val%2=0)
    have eq := unique_at_site Q h4 k (adj hu) hk hw hwk
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hu).2
    have he := only (2*(idx j).val+2) (by have := (idx j).isLt; omega) (by omega)
      (eq ▸ idQ j ▸ hit.mp hj)
    dsimp [idx] at he
    omega
  have allhits {u : V} (hu : u ∈ W) {i : ℕ} (hi : i ≤ 16) (h₀ : i ≠ 0)
      (h : G.Adj (Q.vertex i) u) : ∃ j ∈ hits u, i = 4*j.val+4 := by
    have he := Q.even_of_common c hi (adj hu) h
    let k : Fin 8 := ⟨i/2-1,by omega⟩
    have ek : i = 2*k.val+2 := by dsimp [k]; omega
    have odd := other hu (ek ▸ h)
    let j : Fin 4 := ⟨k.val/2,by have := k.isLt; omega⟩
    have ju : idx j = k := Fin.ext (by dsimp [idx,j]; omega)
    refine ⟨j,hit.mpr ?_,by dsimp [j]; omega⟩
    rw [← idQ j,ju,← ek]; exact h
  have two {u : V} (hu : u ∈ W) : 2 ≤ (hits u).card := by
    by_contra! hh
    obtain ⟨j,hj⟩ := (Finset.mem_filter.mp hu).2
    apply bad j
    refine ⟨u,adj hu,idQ j ▸ hit.mp hj,?_⟩
    intro i hi h₀ h
    obtain ⟨k,hk,ek⟩ := allhits hu hi h₀ h
    have eq := Finset.card_le_one.mp (by omega : (hits u).card ≤ 1) _ hk _ hj
    rw [eq] at ek; dsimp [idx]; omega
  have off {u : V} (hu : u ∈ W) : Off P u (fun i => ∃ j ∈ hits u, i=4*j.val+2) := by
    refine ⟨fun i hi e => hz.2.2 (i+1) (by omega) (by omega) (e ▸ adj hu), ?_⟩
    intro i hi
    constructor
    · intro h
      obtain ⟨j,hj,ej⟩ := allhits hu (i := i+2) (by omega) (by omega) h.symm
      exact ⟨j,hj,by omega⟩
    · rintro ⟨j,hj,rfl⟩; exact (hit.mp hj).symm
  have dis : Disjoint (hits a) (hits b) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    exact hab (unique_at_site Q h4 (idx j) (adj ha) (idQ j ▸ hit.mp hj)
      (adj hb) (idQ j ▸ hit.mp hj'))
  let pt (i : Fin 2) := if i=0 then a else b
  refine ⟨⟨fun i => hits (pt i),pt,?_,?_,by simpa [pt] using hab,by simpa [pt] using dis,?_,?_⟩⟩
  · intro i; dsimp [pt]; split <;> first | exact adj ha | exact adj hb
  · intro i; dsimp [pt]; split <;> first | exact off ha | exact off hb
  · intro i; dsimp [pt]; split <;> first | exact two ha | exact two hb
  · intro j
    let k : Fin 8 := ⟨2*j.val+2,by have := j.isLt; omega⟩
    obtain ⟨s,hzs,hs⟩ := witness k (by dsimp [k]; omega) (outside (by dsimp [k]; omega))
    exact ⟨s,hzs,offCongr hs (by dsimp [k]; omega)⟩

private theorem twoParts : ∀ a b : Finset (Fin 4), Disjoint a b → 2 ≤ a.card → 2 ≤ b.card →
    b = Finset.univ \ a := by decide

private theorem shortOrFixed : ∀ a b : Finset (Fin 4), Disjoint a b → 2 ≤ a.card → 2 ≤ b.card →
    (∃ j : Fin 3, a = {Fin.castSucc j, j.succ} ∨ b = {Fin.castSucc j, j.succ}) ∨
    a={0,2} ∧ b={1,3} ∨ a={1,3} ∧ b={0,2} := by decide

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Two degree-six profiles cannot use the same pair of columns. A shared
pair would also force the complementary pair to coincide, yielding a square. -/
theorem different_six_supports {P : Chain G 14} {z z' : V} (S : SixProfile P z)
    (T : SixProfile P z') (h4 : NoFourCycle G) (hne : z ≠ z') (i j : Fin 2) :
    S.support i ≠ T.support j := by
  have samePoint {i j : Fin 2} (eq : S.support i = T.support j) : S.point i = T.point j := by
    obtain ⟨a,b,ha,hb,hab⟩ := Finset.one_lt_card_iff.mp (show 1 < (S.support i).card from S.two i)
    have diff : P.vertex (4*a.val+2) ≠ P.vertex (4*b.val+2) := by
      intro e
      have h := P.inj (by have := a.isLt; omega) (by have := b.isLt; omega) e
      exact hab (Fin.ext (by omega))
    apply h4 diff
    · exact ((S.off i).contact _ (by have := a.isLt; omega) |>.2 ⟨a,ha,rfl⟩).symm
    · exact ((S.off i).contact _ (by have := b.isLt; omega) |>.2 ⟨b,hb,rfl⟩).symm
    · exact ((T.off j).contact _ (by have := a.isLt; omega) |>.2 ⟨a,eq ▸ ha,rfl⟩).symm
    · exact ((T.off j).contact _ (by have := b.isLt; omega) |>.2 ⟨b,eq ▸ hb,rfl⟩).symm
  have s0 := twoParts _ _ S.disjoint (S.two 0) (S.two 1)
  have s1 := twoParts _ _ S.disjoint.symm (S.two 1) (S.two 0)
  have t0 := twoParts _ _ T.disjoint (T.two 0) (T.two 1)
  have t1 := twoParts _ _ T.disjoint.symm (T.two 1) (T.two 0)
  have impossible {a b : Fin 2} (e₀ : S.support 0 = T.support a) (e₁ : S.support 1 = T.support b) :
      False :=
    S.distinct (h4 hne (S.edges 0) (samePoint e₀ ▸ T.edges a) (S.edges 1) (samePoint e₁ ▸ T.edges b))
  fin_cases i <;> fin_cases j <;> intro h
  · exact impossible h (s0.trans ((congrArg (fun A => Finset.univ \ A) h).trans t0.symm))
  · exact impossible h (s0.trans ((congrArg (fun A => Finset.univ \ A) h).trans t1.symm))
  · exact impossible (s1.trans ((congrArg (fun A => Finset.univ \ A) h).trans t0.symm)) h
  · exact impossible (s1.trans ((congrArg (fun A => Finset.univ \ A) h).trans t1.symm)) h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Supply the vertices of a short-chord detour from two different failed profiles. -/
theorem six_profile_short_chord {P : Chain G 14} (h4 : NoFourCycle G)
    {x y z z' : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (hz' : Good (grow P y hy) z')
    (S : SixProfile P z) (T : SixProfile P z') :
    ∃ (t : ℕ) (v a b g : V), 2 ≤ t ∧ t+4 ≤ 14 ∧ Off P v (fun _ => False) ∧
      Off P a (· = t-2) ∧ Off P b (· = t+2) ∧ Off P g (fun i => i=t ∨ i=t+4) ∧
      G.Adj v a ∧ G.Adj v b ∧ ¬G.Adj v g := by
  let Result := ∃ (t : ℕ) (v a b g : V), 2 ≤ t ∧ t+4 ≤ 14 ∧ Off P v (fun _ => False) ∧
      Off P a (· = t-2) ∧ Off P b (· = t+2) ∧ Off P g (fun i => i=t ∨ i=t+4) ∧
      G.Adj v a ∧ G.Adj v b ∧ ¬G.Adj v g
  have hzz : z ≠ z' := fun e =>
    hz.2.1 1 (by decide) (h4 hxy hz.1 (e ▸ hz'.1) hx.1.symm hy.1.symm)
  have cases {s u r : V} (A : SixProfile P s) (D : SixProfile P u) (hne : s ≠ u)
      (hr : Good P r) (hu : Good (grow P r hr) u) (k : Fin 2) (j : Fin 3)
      (hk : A.support k = {Fin.castSucc j,j.succ}) : Result := by
    have huoff : Off P u (fun _ => False) := ⟨fun i hi => hu.2.1 (i+1) (by omega),
      fun i hi => iff_false_intro (hu.2.2 (i+1) (by omega) (by omega))⟩
    let t := 4*j.val+2
    have gOff : Off P (A.point k) (fun i => i=t ∨ i=t+4) := by
      apply offCongr (A.off k)
      intro i _
      rw [hk]
      simp [t]
      omega
    have huG : ¬G.Adj u (A.point k) := by
      intro hug
      have cover := twoParts _ _ D.disjoint (D.two 0) (D.two 1)
      have existsℓ : ∃ ℓ : Fin 2, Fin.castSucc j ∈ D.support ℓ := by
        by_cases h : Fin.castSucc j ∈ D.support 0
        · exact ⟨0,h⟩
        exact ⟨1,cover ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩⟩
      obtain ⟨ℓ,hℓ⟩ := existsℓ
      have he : A.point k = D.point ℓ := by
        have hpu : P.vertex t ≠ u := (huoff.fresh _ (by have := j.isLt; dsimp [t]; omega)).symm
        apply h4 hpu
        · exact ((gOff.contact _ (by have := j.isLt; dsimp [t]; omega)).2 (Or.inl rfl)).symm
        · exact hug
        · exact ((D.off ℓ).contact _ (by have := j.isLt; dsimp [t]; omega) |>.2 ⟨j.castSucc,hℓ,rfl⟩).symm
        · exact D.edges ℓ
      apply different_six_supports A D h4 hne k ℓ
      ext i
      have read {v : V} (F : SixProfile P v) (l : Fin 2) :
          i ∈ F.support l ↔ G.Adj (F.point l) (P.vertex (4*i.val+2)) := by
        rw [(F.off l).contact _ (by have := i.isLt; omega)]
        refine ⟨fun h => ⟨i,h,rfl⟩,?_⟩
        rintro ⟨ii,hii,hi⟩
        exact (show ii=i from Fin.ext (by omega)) ▸ hii
      rw [read A k,read D ℓ,he]
    obtain ⟨b,hub,hb⟩ := D.privateSite j
    have before : ∃ a, G.Adj u a ∧ Off P a (· = t-2) := by
      by_cases hj : j.val = 0
      · exact ⟨r,hu.1.symm,offCongr (offGood hr) (by dsimp [t]; omega)⟩
      let i : Fin 3 := ⟨j.val-1,by have := j.isLt; omega⟩
      obtain ⟨a,hua,ha⟩ := D.privateSite i
      exact ⟨a,hua,offCongr ha (by dsimp [i,t]; omega)⟩
    obtain ⟨a,hua,ha⟩ := before
    exact ⟨t,u,a,b,A.point k,by dsimp [t]; omega,by have := j.isLt; dsimp [t]; omega,
      huoff,ha,offCongr hb (by dsimp [t]; omega),gOff,hua,hub,huG⟩
  have left := shortOrFixed _ _ S.disjoint (S.two 0) (S.two 1)
  have rght := shortOrFixed _ _ T.disjoint (T.two 0) (T.two 1)
  rcases left with ⟨j,h|h⟩ | hs
  · exact cases S T hzz hy hz' 0 j h
  · exact cases S T hzz hy hz' 1 j h
  rcases rght with ⟨j,h|h⟩ | ht
  · exact cases T S hzz.symm hx hz 0 j h
  · exact cases T S hzz.symm hx hz 1 j h
  have ne := different_six_supports S T h4 hzz
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · exact False.elim (ne 0 0 (hs.1.trans ht.1.symm))
  · exact False.elim (ne 0 1 (hs.1.trans ht.2.symm))
  · exact False.elim (ne 0 1 (hs.1.trans ht.2.symm))
  · exact False.elim (ne 0 0 (hs.1.trans ht.1.symm))

end Wall133
