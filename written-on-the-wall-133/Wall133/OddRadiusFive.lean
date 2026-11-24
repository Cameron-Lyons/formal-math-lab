import Wall133.OddThree
import Wall133.EndpointContact

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

/-- An off-path vertex whose incidences to the indexed path are prescribed. -/
structure Off (P : Chain G n) (z : V) (sites : ℕ → Prop) : Prop where
  fresh : ∀ i ≤ n, z ≠ P.vertex i
  contact : ∀ i ≤ n, G.Adj z (P.vertex i) ↔ sites i

theorem offGood {P : Chain G n} {z : V} (h : Good P z) :
    Off P z (· = 0) := ⟨h.2.1, fun i hi => ⟨fun ha => by
      by_contra hn; exact h.2.2 i hi hn ha, fun he => he ▸ h.1.symm⟩⟩

/-- Replace the internal vertex at index k by a three-vertex detour. -/
def insertDetour (P : Chain G n) (k : ℕ) (hk : 0 < k) (hkn : k < n)
    {a x b : V} (ha : Off P a (fun i => i+1 = k)) (hx : Off P x (fun _ => False))
    (hb : Off P b (fun i => i = k+1)) (hax : G.Adj a x) (hxb : G.Adj x b)
    (hab : a ≠ b) (hab' : ¬G.Adj a b) : Chain G (n+2) where
  vertex i := if i < k then P.vertex i else if i = k then a else if i = k+1 then x
    else if i = k+2 then b else P.vertex (i-2)
  inj := by
    intro i j hi hj
    split_ifs <;> intro e
    all_goals first
      | omega
      | exact (ha.fresh _ (by omega) e).elim
      | exact (ha.fresh _ (by omega) e.symm).elim
      | exact (hx.fresh _ (by omega) e).elim
      | exact (hx.fresh _ (by omega) e.symm).elim
      | exact (hb.fresh _ (by omega) e).elim
      | exact (hb.fresh _ (by omega) e.symm).elim
      | exact (hax.ne e).elim | exact (hax.ne e.symm).elim
      | exact (hxb.ne e).elim | exact (hxb.ne e.symm).elim
      | exact (hab e).elim | exact (hab e.symm).elim
      | have h := P.inj (by omega) (by omega) e; omega
  edges := by
    intro i j hi hj
    have hnab : ¬G.Adj b a := fun h => hab' h.symm
    have back {s : ℕ → Prop} {z : V} (h : Off P z s) (l : ℕ) (hl : l ≤ n) :
        G.Adj (P.vertex l) z ↔ s l := (G.adj_comm _ _).trans (h.contact l hl)
    split_ifs <;> simp (disch := omega) only [ha.contact, hx.contact, hb.contact,
      back ha, back hx, back hb, P.edges, G.loopless.irrefl, hax, hax.symm,
      hxb, hxb.symm, hab', hnab, true_iff, false_iff] <;> omega

def tailChain (P : Chain G n) : Chain G (n-1) where
  vertex i := P.vertex (i+1)
  inj := by
    intro i j hi hj e
    by_cases hn : n = 0
    · omega
    have h := P.inj (by omega) (by omega) e
    omega
  edges := by
    intro i j hi hj
    by_cases hn : n = 0
    · have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst i; subst j; simp
    rw [P.edges (by omega) (by omega)]; omega

theorem offTail {P : Chain G n} {z : V} {s : ℕ → Prop} (h : Off P z s)
    (hn : 0 < n) : Off (tailChain P) z (fun i => s (i+1)) :=
  ⟨fun i hi => h.fresh _ (by omega), fun i hi => h.contact _ (by omega)⟩

theorem offCongr {P : Chain G n} {z : V} {s t : ℕ → Prop} (h : Off P z s)
    (eq : ∀ i ≤ n, s i ↔ t i) : Off P z t :=
  ⟨h.fresh, fun i hi => (h.contact i hi).trans (eq i hi)⟩

theorem offInsert {P : Chain G n} {k : ℕ} {hk : 0 < k} {hkn : k < n}
    {a x b : V} {ha : Off P a (fun i => i+1 = k)} {hx : Off P x (fun _ => False)}
    {hb : Off P b (fun i => i = k+1)} {hax : G.Adj a x} {hxb : G.Adj x b}
    {hab : a ≠ b} {hab' : ¬G.Adj a b} {z : V} {s t : ℕ → Prop}
    (hz : Off P z s) (hza : z ≠ a) (hzx : z ≠ x) (hzb : z ≠ b)
    (hza' : ¬G.Adj z a) (hzx' : ¬G.Adj z x) (hzb' : ¬G.Adj z b)
    (hs : ∀ i ≤ n+2, (if i < k then s i else if i ≤ k+2 then False else s (i-2)) ↔ t i) :
    Off (insertDetour P k hk hkn ha hx hb hax hxb hab hab') z t := by
  constructor
  · intro i hi
    dsimp [insertDetour]
    split_ifs <;> first | assumption | exact hz.fresh _ (by omega)
  · intro i hi
    rw [← hs i hi]; dsimp [insertDetour]
    split_ifs <;> first | exact hz.contact _ (by omega) | omega | solve | simp [*]

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem contactOnSuffix (P : Chain G n) {m r j : ℕ} (Q : Chain G m)
    (hr : 0 < r) (hj : 2 ≤ j) (hjn : j ≤ n) (hjm : n+r ≤ m)
    (hsuf : ∀ i ≤ n, Q.vertex (i+r) = P.vertex i)
    (hroot : ∀ i ≤ n, G.Adj (Q.vertex 0) (P.vertex i) → i = 0)
    (k : Fin (m/2)) (heq : 2*k.val+2 = j+r) (hp : PrivateContact Q k) :
    ∃ w, G.Adj (Q.vertex 0) w ∧ Off P w (· = j) := by
  obtain ⟨w, hw, hsite, honly⟩ := hp
  rw [heq, hsuf j hjn] at hsite
  refine ⟨w, hw, ?_, ?_⟩
  · intro i hi eq
    have hi0 := hroot i hi (eq ▸ hw)
    have hedge := (P.edges (Nat.zero_le _) hjn).1 (hi0 ▸ eq ▸ hsite.symm)
    omega
  · intro i hi
    refine ⟨fun h => ?_, fun e => e ▸ hsite.symm⟩
    have hi' : i+r ≤ m := by omega
    have e := honly (i+r) hi' (by omega) (hsuf i hi ▸ h.symm)
    omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem color_common (c : G.Coloring (Fin 2)) {a b x : V}
    (ha : G.Adj a x) (hb : G.Adj b x) : c a = c b := by
  apply Fin.ext
  have := Fin.val_ne_of_ne (c.valid ha)
  have := Fin.val_ne_of_ne (c.valid hb)
  have := (c a).isLt; have := (c b).isLt; have := (c x).isLt
  omega

omit [DecidableEq V] in
private theorem firstLevel (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {x : V} (hx : Good P x) (hd : (n+1)/2 ≤ G.degree x)
    (sx : ∀ z, ¬Good (grow P x hx) z) {j : ℕ} (hj : 2 ≤ j) (hjn : j ≤ n)
    (he : (j+1)%2 = 0) : ∃ b, G.Adj x b ∧ Off P b (· = j) := by
  let k : Fin ((n+1)/2) := ⟨(j+1)/2-1, by omega⟩
  apply contactOnSuffix P (grow P x hx) (r := 1) (by omega) hj hjn (by omega)
    (fun _ _ => rfl) (fun i hi ha => ((offGood hx).contact i hi).mp ha) k
    (by dsimp [k]; omega)
  exact saturated_witness _ c h4 (by omega) hd sx k

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Drop the initial vertex and replace one internal vertex by a detour.
The second good neighbor stays disjoint from this path, and its contacts
beyond the detour move forward by one index. -/
theorem singleDetour (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {u : ℕ} (hu : 1 ≤ u) (hun : u+2 ≤ n)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (w₁ : ∃ a, G.Adj x a ∧ Off P a (· = u))
    (w₂ : ∃ b, G.Adj x b ∧ Off P b (· = u+2)) :
    ∃ R : Chain G (n-1+2), R.vertex (n-1+2) = P.vertex n ∧ Off R y (fun _ => False) ∧
      ∀ {z : V} {j : ℕ}, u+2 ≤ j → G.Adj y z → Off P z (· = j) → Off R z (· = j+1) := by
  obtain ⟨a,hxa,ha⟩ := w₁
  obtain ⟨b,hxb,hb⟩ := w₂
  have rows : c x = c y := color_common c hx.1.symm hy.1.symm
  have ca : c a = c (P.vertex 0) := color_common c hxa.symm hx.1
  have cb : c b = c (P.vertex 0) := color_common c hxb.symm hx.1
  have noEdge {u v : V} (heq : c u = c v) : ¬G.Adj u v := fun e => c.valid e heq
  have cross {u : V} (hu : u ≠ P.vertex 0) : ¬(G.Adj x u ∧ G.Adj y u) :=
    fun ⟨hxu, hyu⟩ => hu (h4 hxy hxu hyu hx.1.symm hy.1.symm)
  have hab : a ≠ b := by
    intro eq
    have := (hb.contact u (by omega)).1 (eq ▸ (ha.contact u (by omega)).2 rfl)
    omega
  let T := tailChain P
  have ht : 0 < n := by omega
  have hA : Off T a (fun i => i+1 = u) := offTail ha ht
  have hB : Off T b (fun i => i = u+1) := offCongr (offTail hb ht) (by omega)
  have hX : Off T x (fun _ => False) := offCongr (offTail (offGood hx) ht) (by simp)
  let R := insertDetour T u (by omega) (by omega) hA hX hB hxa.symm hxb hab
    (noEdge (ca.trans cb.symm))
  have hY : Off R y (fun _ => False) := by
    apply offInsert (offTail (offGood hy) ht)
    · exact fun e => (c.valid hy.1) (ca.symm.trans (congrArg c e).symm)
    · exact hxy.symm
    · exact fun e => (c.valid hy.1) (cb.symm.trans (congrArg c e).symm)
    · exact fun e => cross (ha.fresh 0 (by omega)) ⟨hxa,e⟩
    · exact noEdge rows.symm
    · exact fun e => cross (hb.fresh 0 (by omega)) ⟨hxb,e⟩
    · intro i hi; split_ifs <;> simp
  have next {z : V} {j : ℕ} (hyz : G.Adj y z) (hz : Off P z (· = j)) :
      Off R z (fun i => if i < u then i+1=j else if i ≤ u+2 then False else i-2+1=j) := by
    apply offInsert (offTail hz ht)
    · exact fun e => cross (hz.fresh 0 (by omega)) ⟨e ▸ hxa,hyz⟩
    · exact fun e => (c.valid hyz) (rows.symm.trans (congrArg c e).symm)
    · exact fun e => cross (hz.fresh 0 (by omega)) ⟨e ▸ hxb,hyz⟩
    · exact noEdge ((color_common c hyz.symm hy.1).trans ca.symm)
    · exact fun e => cross (hz.fresh 0 (by omega)) ⟨e.symm,hyz⟩
    · exact noEdge ((color_common c hyz.symm hy.1).trans cb.symm)
    · intro i hi; rfl
  refine ⟨R, ?_, hY, ?_⟩
  · change (if n-1+2 < u then _ else _) = _
    simp only [show ¬n-1+2 < u by omega, show ¬n-1+2 = u by omega,
      show ¬n-1+2 = u+1 by omega, show ¬n-1+2 = u+2 by omega, if_false]
    change P.vertex (n-1+2-2+1) = P.vertex n
    congr 1
    omega
  · intro z j hj hz hOff
    apply offCongr (next hz hOff)
    intro i hi
    split_ifs <;> simp_all <;> omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem twoDetours (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {u v : ℕ} (hu : 1 ≤ u) (huv : u+2 ≤ v) (hvn : v+2 ≤ n)
    {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (w₁ : ∃ a, G.Adj x a ∧ Off P a (· = u))
    (w₂ : ∃ b, G.Adj x b ∧ Off P b (· = u+2))
    (w₃ : ∃ p, G.Adj y p ∧ Off P p (· = v))
    (w₄ : ∃ q, G.Adj y q ∧ Off P q (· = v+2)) :
    ∃ F : Chain G (n+3), F.vertex (n+3) = P.vertex n := by
  obtain ⟨R,hR,hY,next⟩ := singleDetour P c h4 hu (by omega) hx hy hxy w₁ w₂
  obtain ⟨p,hyp,hp⟩ := w₃
  obtain ⟨q,hyq,hq⟩ := w₄
  have cp : c p = c q := color_common c hyp.symm hyq.symm
  have hpq : p ≠ q := by
    intro eq
    have := (hq.contact v (by omega)).1 (eq ▸ (hp.contact v (by omega)).2 rfl)
    omega
  have hP' : Off R p (fun i => i+1 = v+2) := offCongr (next huv hyp hp) (by omega)
  have hQ' : Off R q (fun i => i = v+2+1) := next (by omega) hyq hq
  let F := insertDetour R (v+2) (by omega) (by omega) hP' hY hQ' hyp.symm hyq
    hpq (fun h => c.valid h cp)
  have eq : n-1+2+2 = n+3 := by omega
  refine ⟨eq ▸ F, ?_⟩
  have cast_vertex {i j : ℕ} (e : i = j) (D : Chain G i) (s : ℕ) :
      (e ▸ D : Chain G j).vertex s = D.vertex s := by subst j; rfl
  rw [cast_vertex eq F]
  change (if n+3 < v+2 then _ else _) = _
  simp only [show ¬n+3 < v+2 by omega, show ¬n+3 = v+2 by omega,
    show ¬n+3 = v+2+1 by omega, show ¬n+3 = v+2+2 by omega, if_false]
  convert hR using 2
  omega

omit [DecidableEq V] in
theorem doubleStallsWithEnd (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 7 ≤ n) {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hdx : (n+1)/2 ≤ G.degree x) (hdy : (n+1)/2 ≤ G.degree y)
    (sx : ∀ z, ¬Good (grow P x hx) z) (sy : ∀ z, ¬Good (grow P y hy) z) :
    ∃ F : Chain G (n+3), F.vertex (n+3) = P.vertex n := by
  exact twoDetours P c h4 (u := 3) (v := 5) (by omega) (by omega) (by omega) hx hy hxy
    (firstLevel P c h4 hx hdx sx (by omega) (by omega) rfl)
    (firstLevel P c h4 hx hdx sx (by omega) (by omega) rfl)
    (firstLevel P c h4 hy hdy sy (by omega) (by omega) rfl)
    (firstLevel P c h4 hy hdy sy (by omega) (by omega) rfl)

theorem path_of_two_step_pair (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {x y z : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (j k : Fin ((n+2)/2)) (hj : 1 ≤ j.val) (hjk : k.val = j.val+1)
    (pj : PrivateContact (grow (grow P x hx) z hz) j)
    (pk : PrivateContact (grow (grow P x hx) z hz) k) : n+4 ≤ G.path := by
  let Q := grow (grow P x hx) z hz
  have witness {ℓ : Fin ((n+2)/2)} (hℓ : 1 ≤ ℓ.val) (hp : PrivateContact Q ℓ) :
      ∃ b, G.Adj z b ∧ Off P b (· = 2*ℓ.val) :=
    contactOnSuffix P Q (r := 2) (by omega) (by omega) (by have := ℓ.isLt; omega)
      (by omega) (fun _ _ => rfl)
      (fun i hi h => False.elim (hz.2.2 (i+1) (by omega) (by omega) h)) ℓ rfl hp
  let pos := 2*j.val
  have hk := k.isLt
  obtain ⟨a,hza,ha⟩ := witness hj pj
  obtain ⟨b,hzb,hb'⟩ := witness (by omega : 1 ≤ k.val) pk
  have hb : Off P b (· = pos+2) := offCongr hb' (by dsimp [pos]; omega)
  have hpos : pos+2 ≤ n := by dsimp [pos]; omega
  have hzx : G.Adj x z := hz.1
  have hnz : z ≠ P.vertex 0 := hz.2.1 1 (by omega)
  have hzy : ¬G.Adj z y := fun h => hnz (h4 hxy hzx h.symm hx.1.symm hy.1.symm)
  have ca : c a = c x := color_common c hza.symm hzx
  have cb : c b = c x := color_common c hzb.symm hzx
  have cy : c y = c x := color_common c hy.1.symm hx.1.symm
  have hAB : a ≠ b := by
    intro eq
    have := (hb.contact pos (by omega)).1 (eq ▸ (ha.contact pos (by omega)).2 rfl)
    omega
  let T := grow P y hy
  have off {u : V} {j : ℕ} (hu : Off P u (· = j)) (hzu : G.Adj z u)
      (hcol : c u = c y) : Off T u (· = j+1) := by
    constructor
    · intro i hi
      cases i with
      | zero => exact fun eq => hzy ((show u = y from eq) ▸ hzu)
      | succ i => exact hu.fresh i (by omega)
    · intro i hi
      cases i with
      | zero => exact ⟨fun h => False.elim (c.valid h hcol), by omega⟩
      | succ i => exact (hu.contact i (by omega)).trans (by omega)
  have hA : Off T a (fun i => i+1 = pos+2) :=
    offCongr (off ha hza (ca.trans cy.symm)) (by dsimp [pos]; omega)
  have hB : Off T b (fun i => i = pos+2+1) := off hb hzb (cb.trans cy.symm)
  have hZ : Off T z (fun _ => False) := by
    constructor
    · intro i hi
      cases i with
      | zero => exact fun eq => (c.valid hzx) (cy.symm.trans (congrArg c eq).symm)
      | succ i => exact hz.2.1 (i+1) (by omega)
    · intro i hi
      cases i with
      | zero => exact iff_false_intro hzy
      | succ i => exact iff_false_intro (hz.2.2 (i+1) (by omega) (by omega))
  exact (insertDetour T (pos+2) (by omega) (by omega) hA hZ hB hza.symm hzb hAB
    (fun h => c.valid h (ca.trans cb.symm))).length_le

theorem secondLevel (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 4 ≤ n) {x y z : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (hdz : (n+2)/2 ≤ G.degree z ∨
      (6 ≤ (n+2)/2 ∨ 5 ≤ (n+2)/2 ∧ n%2=0) ∧ (n+2)/2 ≤ G.degree z + 1) :
    n+4 ≤ G.path := by
  let Q := grow (grow P x hx) z hz
  by_cases hs : ∃ w, Good Q w
  · obtain ⟨w, hw⟩ := hs
    exact (grow Q w hw).length_le
  have witness {ℓ : Fin ((n+2)/2)} (hℓ : 1 ≤ ℓ.val) (hp : PrivateContact Q ℓ) :
      ∃ b, G.Adj z b ∧ Off P b (· = 2*ℓ.val) :=
    contactOnSuffix P Q (r := 2) (by omega) (by omega) (by have := ℓ.isLt; omega)
      (by omega) (fun _ _ => rfl)
      (fun i hi h => False.elim (hz.2.2 (i+1) (by omega) (by omega) h)) ℓ rfl hp
  by_cases hshort : n+4 ≤ G.path
  · exact hshort
  have pair : ∃ j k : Fin ((n+2)/2), 1 ≤ j.val ∧ k.val = j.val+1 ∧
      PrivateContact Q j ∧ PrivateContact Q k := by
    rcases hdz with full | ⟨hl,hslack⟩
    · exact ⟨⟨1,by omega⟩,⟨2,by omega⟩,Nat.le_refl 1,rfl,
        saturated_witness Q c h4 (by omega) full (fun w hw => hs ⟨w,hw⟩) _,
        saturated_witness Q c h4 (by omega) full (fun w hw => hs ⟨w,hw⟩) _⟩
    · obtain ⟨a,b,known⟩ := near_saturation Q c h4 (by omega) hslack (fun w hw => hs ⟨w,hw⟩)
      have exception (i : Fin ((n+2)/2)) (hi : 1 ≤ i.val) (hend : 2*i.val=2 ∨ 2*i.val=n) :
          i.val = a.val ∨ i.val = b.val := by
        by_contra! he
        obtain ⟨u,hzu,hu⟩ := witness hi (known i (fun h => he.1 (congrArg Fin.val h))
          (fun h => he.2 (congrArg Fin.val h)))
        exact hshort (path_of_private_end P c h4 (by omega) hx hy hxy hz hzu _ hend hu.fresh hu.contact)
      have first := exception ⟨1,by omega⟩ (by change 1 ≤ 1; decide) (Or.inl rfl)
      change 1 = a.val ∨ 1 = b.val at first
      rcases hl with hlarge | ⟨hmid,heven⟩
      · have ex : ∃ i : ℕ, 2 ≤ i ∧ i+1 < (n+2)/2 ∧ i ≠ a.val ∧ i ≠ b.val ∧
            i+1 ≠ a.val ∧ i+1 ≠ b.val := by
          by_contra! h
          have := h 2 (by omega) (by omega)
          have := h 4 (by omega) (by omega)
          omega
        obtain ⟨i,hi,hij,h2a,h2b,h3a,h3b⟩ := ex
        exact ⟨⟨i,by omega⟩,⟨i+1,hij⟩,by change 1 ≤ i; omega,rfl,
          known _ (fun h => h2a (congrArg Fin.val h)) (fun h => h2b (congrArg Fin.val h)),
          known _ (fun h => h3a (congrArg Fin.val h)) (fun h => h3b (congrArg Fin.val h))⟩
      have last := exception ⟨n/2,by omega⟩ (by change 1 ≤ n/2; omega) (Or.inr (by change 2*(n/2)=n; omega))
      change n/2 = a.val ∨ n/2 = b.val at last
      refine ⟨⟨2,by omega⟩,⟨3,by omega⟩,by change 1 ≤ 2; decide,rfl,?_,?_⟩
      · apply known <;> intro e <;> have he := congrArg Fin.val e <;>
          change 2 = _ at he <;> omega
      · apply known <;> intro e <;> have he := congrArg Fin.val e <;>
          change 3 = _ at he <;> omega
  obtain ⟨j,k,hj,hjk,pj,pk⟩ := pair
  exact path_of_two_step_pair P c h4 hx hy hxy hz j k hj hjk pj pk

/-- In an asymmetric core, two clean neighbors of the high-degree root force
an extra three edges beyond the path of length twice the minimum degree. -/
private theorem path_of_high_vertex (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V)
    (hv : d+2 ≤ G.degree v) (hhigh : 4 ≤ d ∨ ∀ x, c x = c v → d < G.degree x) :
    2*d+4 ≤ G.path := by
  obtain ⟨R,hR⟩ := exists_chain_ending_at v c h4 (by omega) hmin (2*d) le_rfl
  let P := R.reverse
  have hP : P.vertex 0 = v := by simpa [P, Chain.reverse] using hR
  obtain ⟨x,y,hx,hy,hxy⟩ :=
    two_good P c h4 (by omega) (by rw [hP]; omega)
  have go {u w z : V} (hu : Good P u) (hw : Good P w) (huw : u ≠ w)
      (hz : Good (grow P u hu) z) : 2*d+4 ≤ G.path := by
    have hzu : G.Adj u z := hz.1
    have col : c z = c v := hP ▸ color_common c hzu.symm hu.1
    apply secondLevel P c h4 (by omega) hu hw huw hz
    rcases hhigh with hlarge | hclass
    · have := hmin z; exact Or.inr (by omega)
    · have := hclass z col; exact Or.inl (by omega)
  by_cases sx : ∃ z, Good (grow P x hx) z
  · obtain ⟨z,hz⟩ := sx
    exact go hx hy hxy hz
  by_cases sy : ∃ z, Good (grow P y hy) z
  · obtain ⟨z,hz⟩ := sy
    exact go hy hx hxy.symm hz
  by_cases h3 : d = 3
  · subst d
    have col : c (P.vertex 6) = c v := by
      rw [← hP]; apply Fin.ext
      have := P.color_val c 6 (by decide)
      have := (c (P.vertex 0)).isLt
      omega
    exact ten_le_path_of_two_stalls P c h4 hx hy hxy (hmin x) (hmin y)
      (hhigh.resolve_left (by omega) _ col) (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)
  obtain ⟨F,_⟩ := doubleStallsWithEnd P c h4 (by omega) hx hy hxy (by have := hmin x; omega)
    (by have := hmin y; omega) (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)
  exact F.length_le

/-- The asymmetric minimum-degree bound at every d ≥ 3. -/
theorem odd_path_of_high_vertex (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V)
    (hv : d+2 ≤ G.degree v) (hhigh : ∀ x, c x = c v → d < G.degree x) :
    2*d+4 ≤ G.path :=
  path_of_high_vertex c h4 hd hmin v hv (.inr hhigh)

/-- At minimum degree at least four the path bound needs only one high-degree
vertex and applies to both color classes. -/
theorem two_mul_minDegree_add_four_of_high_vertex (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (v : V)
    (hv : d+2 ≤ G.degree v) : 2*d+4 ≤ G.path :=
  path_of_high_vertex c h4 (by omega) hmin v hv (.inl hd)

omit [DecidableEq V] in
theorem chain_odd_ending_at (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {d : ℕ}
    (hd : 4 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (col : Fin 2)
    (hc : ∀ x, c x = col → d+1 ≤ G.degree x) (v : V) :
    ∃ P : Chain G (2*d+1), P.vertex (2*d+1) = v := by
  by_cases hv : c v = col
  · obtain ⟨R,hR⟩ := exists_chain_ending_at v c h4 (by omega) hmin (2*d) le_rfl
    have he : c (R.vertex 0) = col := by
      apply Fin.ext
      have h := R.color_val c (2*d) le_rfl
      rw [hR, hv] at h
      have := (c (R.vertex 0)).isLt
      omega
    have hh := hc _ he
    obtain ⟨F,hF⟩ := R.extend c h4 (by omega) (by omega)
    exact ⟨F,hF.trans hR⟩
  · let n := 2*d-1
    obtain ⟨R,hR⟩ := exists_chain_ending_at v c h4 (by omega) hmin n (by dsimp [n]; omega)
    have he : c (R.vertex 0) = col := by
      apply Fin.ext
      have h := R.color_val c n le_rfl
      rw [hR] at h
      have := (c (R.vertex 0)).isLt; have := (c v).isLt; have := col.isLt
      have := Fin.val_ne_of_ne hv
      dsimp [n] at h
      omega
    have hh := hc _ he
    have eq : n+2 = 2*d+1 := by dsimp [n]; omega
    have castEnd {i j : ℕ} (e : i = j) (F : Chain G i) (hf : F.vertex i = v) :
        ∃ Q : Chain G j, Q.vertex j = v := by subst j; exact ⟨F,hf⟩
    obtain ⟨x,y,hx,hy,hxy⟩ := two_good R c h4 (by dsimp [n]; omega) (by dsimp [n]; omega)
    have go {w z : V} (hw : Good R w) (hz : Good (grow R w hw) z) :
        ∃ Q : Chain G (2*d+1), Q.vertex (2*d+1) = v := by
      apply castEnd eq (grow (grow R w hw) z hz)
      exact hR
    by_cases sx : ∃ z, Good (grow R x hx) z
    · obtain ⟨z,hz⟩ := sx; exact go hx hz
    by_cases sy : ∃ z, Good (grow R y hy) z
    · obtain ⟨z,hz⟩ := sy; exact go hy hz
    obtain ⟨F,hF⟩ := doubleStallsWithEnd R c h4 (by dsimp [n]; omega) hx hy hxy
      (by have := hmin x; dsimp [n]; omega) (by have := hmin y; dsimp [n]; omega)
      (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)
    exact castEnd (by omega : n+3-1 = 2*d+1) (tailChain F) (hF.trans hR)

theorem looseDoubleStalls (P : Chain G n) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 8 ≤ (n+1)/2) {x y : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hdx : (n+1)/2 ≤ G.degree x+1) (hdy : (n+1)/2 ≤ G.degree y+1)
    (sx : ∀ z, ¬Good (grow P x hx) z) (sy : ∀ z, ¬Good (grow P y hy) z) :
    n+4 ≤ G.path := by
  let Pair (w : V) (j : ℕ) := (∃ a, G.Adj w a ∧ Off P a (· = 2*j+1)) ∧
    (∃ b, G.Adj w b ∧ Off P b (· = 2*j+1+2))
  have pair {w : V} (hw : Good P w) (hd : (n+1)/2 ≤ G.degree w+1)
      (sw : ∀ z, ¬Good (grow P w hw) z) (avoid : ℕ) :
      ∃ j : Fin ((n+1)/2), 1 ≤ j.val ∧ j.val ≠ avoid ∧ 2*j.val+3 ≤ n ∧ Pair w j.val := by
    obtain ⟨j,k,hj,hja,hjk,pj,pk⟩ := private_pair_avoiding (grow P w hw) c h4 hn avoid hd sw
    have hk := k.isLt
    have wit {i : Fin ((n+1)/2)} (hi : 1 ≤ i.val) (hp : PrivateContact (grow P w hw) i) :
        ∃ z, G.Adj w z ∧ Off P z (· = 2*i.val+1) :=
      contactOnSuffix P (grow P w hw) (r := 1) (by omega) (by omega)
        (by have := i.isLt; omega) (by omega) (fun _ _ => rfl)
        (fun s hs ha => ((offGood hw).contact s hs).mp ha) i (by omega) hp
    obtain ⟨z,hz,hoff⟩ := wit (by omega : 1 ≤ k.val) pk
    exact ⟨j,hj,hja,by omega,wit hj pj,z,hz,offCongr hoff (by omega)⟩
  obtain ⟨j,hj,_,hjn,ax,bx⟩ := pair hx hdx sx 0
  obtain ⟨k,hk,hkj,hkn,ay,by'⟩ := pair hy hdy sy j.val
  by_cases hjk : j.val < k.val
  · obtain ⟨F,_⟩ := twoDetours P c h4 (u := 2*j.val+1) (v := 2*k.val+1)
      (by omega) (by omega) (by omega) hx hy hxy ax bx ay by'
    exact F.length_le
  · obtain ⟨F,_⟩ := twoDetours P c h4 (u := 2*k.val+1) (v := 2*j.val+1)
      (by omega) (by omega) (by omega) hy hx hxy.symm ay by' ax bx
    exact F.length_le

/-- An asymmetric minimum degree supplies another edge at the far end of
the rooted path, after which two near-saturated rows give the detours. -/
theorem odd_core_add_five_le_path (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 8 ≤ d) (hmin : ∀ x, d ≤ G.degree x) (col : Fin 2)
    (hside : ∀ x, c x = col → d+1 ≤ G.degree x) (v : V)
    (hv : d+2 ≤ G.degree v) : 2*d+5 ≤ G.path := by
  obtain ⟨R,hR⟩ := chain_odd_ending_at c h4 (by omega) hmin col hside v
  let P := R.reverse
  have hP : P.vertex 0 = v := by simpa [P,Chain.reverse] using hR
  obtain ⟨x,y,hx,hy,hxy⟩ := two_good P c h4 (by omega) (by rw [hP]; omega)
  have go {u w z : V} (hu : Good P u) (hw : Good P w) (huw : u ≠ w)
      (hz : Good (grow P u hu) z) : 2*d+5 ≤ G.path := by
    apply secondLevel P c h4 (by omega) hu hw huw hz
    have := hmin z
    exact .inr (by omega)
  by_cases sx : ∃ z, Good (grow P x hx) z
  · obtain ⟨z,hz⟩ := sx; exact go hx hy hxy hz
  by_cases sy : ∃ z, Good (grow P y hy) z
  · obtain ⟨z,hz⟩ := sy; exact go hy hx hxy.symm hz
  exact looseDoubleStalls P c h4 (by omega) hx hy hxy
    (by have := hmin x; omega) (by have := hmin y; omega)
    (fun z hz => sx ⟨z,hz⟩) (fun z hz => sy ⟨z,hz⟩)

end Wall133
