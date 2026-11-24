import Wall133.BipartiteGeodesic
import Wall133.BipartiteRadiusSix

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

def Chain.metricSuffix (P : Chain G n) (t : ℕ) : Prop :=
  ∀ i, t ≤ i → i ≤ n → G.dist (P.vertex i) (P.vertex n) = n-i

noncomputable def geoCode (P : Chain G n) (t i : ℕ) : ℕ :=
  if i < t then i/2-1 else (t-1)/2 + (i-(n-(G.dist (P.vertex 0) (P.vertex n)+2)))/2

theorem Chain.suffixCode (P : Chain G n) (hc : G.Connected) {t : ℕ} (hm : P.metricSuffix t) :
    (∀ i, P.Blocks i → geoCode P t i < (t-1)/2+3) ∧
    ∀ i j, P.Blocks i → P.Blocks j → geoCode P t i = geoCode P t j → i=j := by
  let b := n-(G.dist (P.vertex 0) (P.vertex n)+2)
  have window (i) (hi : P.Blocks i) (hg : t ≤ i) : b ≤ i ∧ i ≤ b+4 := by
    obtain ⟨hn,_,_,hd⟩ := hi
    have h₁ := hc.dist_triangle (u := P.vertex 0) (v := P.vertex i) (w := P.vertex n)
    have h₂ := hc.dist_triangle (u := P.vertex i) (v := P.vertex 0) (w := P.vertex n)
    rw [G.dist_comm (u := P.vertex i) (v := P.vertex 0)] at h₂
    rw [hm _ hg hn] at h₁ h₂
    dsimp [b]; omega
  constructor
  · intro i hi
    have := hi.2.1; have := hi.2.2.1
    change (if i<t then i/2-1 else (t-1)/2+(i-b)/2) < _
    split_ifs <;> first | omega | (have := window i hi (by omega); omega)
  · intro i j hi hj h
    have := hi.2.1; have := hi.2.2.1; have := hj.2.1; have := hj.2.2.1
    change (if i<t then i/2-1 else (t-1)/2+(i-b)/2) =
      (if j<t then j/2-1 else (t-1)/2+(j-b)/2) at h
    split_ifs at h <;> first | omega | (have := window i hi (by omega); have := window j hj (by omega); omega)

/-- At equality every available code represents a neighbor which is blocked
at a unique index of the path. -/
theorem Chain.private_of_code (P : Chain G n) (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (hn : 2 ≤ n) (N : Finset V)
    (ha : ∀ w ∈ N, G.Adj (P.vertex 0) w) (sat : ∀ w ∈ N, ¬ Good P w)
    (f : ℕ → ℕ) {m : ℕ} (hd : m ≤ N.card) (bound : ∀ i, P.Blocks i → f i < m)
    (inj : ∀ i j, P.Blocks i → P.Blocks j → f i = f j → i=j) (k : Fin m) :
    ∃ w ∈ N, ∃ i, P.Blocks i ∧ f i = k.val ∧ G.Adj (P.vertex i) w ∧
      ∀ j ≤ n, j ≠ 0 → G.Adj (P.vertex j) w → j=i := by
  classical
  have block {z : V} (hz : z ∈ N) {i : ℕ} (hi : i ≤ n) (hpos : i ≠ 0)
      (hw : G.Adj (P.vertex i) z) : P.Blocks i := by
    refine ⟨hi,hpos,P.even_of_common c hi (ha _ hz) hw,?_⟩
    have h := hc.dist_triangle (u := P.vertex 0) (v := z) (w := P.vertex i)
    simpa only [dist_eq_one_iff_adj.mpr (ha _ hz), dist_eq_one_iff_adj.mpr hw.symm] using h
  choose idx hidx using (fun z : N => blocker P c hn (ha _ z.property) (sat _ z.property))
  let i (z : N) := 2*(idx z).val+2
  have hI (z : N) : P.Blocks (i z) := block z.property
    (by dsimp [i]; have := (idx z).isLt; omega) (by dsimp [i]; omega) (hidx z)
  let F (z : N) : Fin m := ⟨f (i z),bound _ (hI z)⟩
  have unique {u v : N} {j : ℕ} (hj : P.Blocks j) (hu : G.Adj (P.vertex j) u.val)
      (hv : G.Adj (P.vertex j) v.val) : u=v := by
    apply Subtype.ext
    exact h4 (x := P.vertex 0) (y := P.vertex j) (fun e => hj.2.1 ((P.inj (Nat.zero_le _) hj.1 e).symm))
      (ha _ u.property) hu (ha _ v.property) hv
  have fi : Function.Injective F := by
    intro u v he
    have eq := inj _ _ (hI u) (hI v) (congrArg Fin.val he)
    exact unique (hI u) (hidx u) (eq ▸ hidx v)
  have fs : Function.Surjective F := by
    apply ((Fintype.bijective_iff_injective_and_card F).2 ⟨fi,?_⟩).2
    apply (Fintype.card_le_of_injective F fi).antisymm
    simpa only [Fintype.card_coe, Fintype.card_fin] using hd
  obtain ⟨w,hw⟩ := fs k
  refine ⟨w,w.property,i w,hI w,congrArg Fin.val hw,hidx w,?_⟩
  intro j hj hpos he
  have hb := block w.property hj hpos he
  obtain ⟨v,hv⟩ := fs ⟨f j,bound _ hb⟩
  have eq := inj _ _ (hI v) hb (congrArg Fin.val hv)
  have vw : v=w := unique hb (eq ▸ hidx v) he
  exact vw ▸ eq.symm

/-- Rotation about a private contact at index k preserves the old suffix
from k onward and moves the endpoint to the old index k-2. -/
def Chain.rotateAt (P : Chain G n) (k : ℕ) (hk : 4 ≤ k) (hkn : k ≤ n) {w : V}
    (ha : G.Adj (P.vertex 0) w) (hb : G.Adj (P.vertex k) w)
    (honly : ∀ i ≤ n, i ≠ 0 → G.Adj (P.vertex i) w → i=k) : Chain G n where
  vertex i := if k ≤ i then P.vertex i else if i+1=k then w else P.vertex (k-2-i)
  inj := by
    have fresh (i) (hi : i ≤ n) : w ≠ P.vertex i := by
      intro e
      have := (P.edges (Nat.zero_le _) hi).1 (e ▸ ha)
      have := (P.edges hkn hi).1 (e ▸ hb)
      omega
    intro i j hi hj
    split_ifs <;> intro e
    all_goals first
      | omega
      | exact (fresh _ (by omega) e).elim
      | exact (fresh _ (by omega) e.symm).elim
      | have := P.inj (by omega) (by omega) e; omega
  edges := by
    have adj (i) (hi : i ≤ n) : G.Adj (P.vertex i) w ↔ i=0 ∨ i=k := by
      constructor
      · intro h; by_cases e : i=0
        · exact Or.inl e
        · exact Or.inr (honly i hi e h)
      · rintro (rfl|rfl)
        · exact ha
        · exact hb
    intro i j hi hj
    split_ifs
    all_goals first
      | rw [P.edges (by omega) (by omega)]; omega
      | rw [adj _ (by omega)]; omega
      | rw [G.adj_comm, adj _ (by omega)]; omega
      | simp only [SimpleGraph.irrefl, false_iff]; omega
      | exact P.edges hi hj

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
theorem longest_seed (T : Chain G n) (S : Finset V) (hs : T.vertex 0 ∈ S) :
    ∃ t, ∃ P : Chain G (t+n), P.vertex 0 ∈ S ∧ (∀ i ≤ n, P.vertex (t+i)=T.vertex i) ∧
      (∀ i < t, P.vertex i ∈ S) ∧ ∀ z ∈ S, ¬Good P z := by
  classical
  let E (t : ℕ) := ∃ P : Chain G (t+n), P.vertex 0 ∈ S ∧ (∀ i ≤ n, P.vertex (t+i)=T.vertex i) ∧ ∀ i < t, P.vertex i ∈ S
  let F := (Finset.range (G.path+1)).filter E
  have feasible {t} (h : E t) : t ∈ F := by
    obtain ⟨P,hP⟩ := h
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := P.length_le; omega),P,hP⟩
  have h0 : E 0 := by
    unfold E; rw [Nat.zero_add]; simp only [Nat.zero_add]
    exact ⟨T,hs,fun _ _ => rfl,by omega⟩
  obtain ⟨t,ht,hmax⟩ := Finset.exists_max_image F id ⟨0,feasible h0⟩
  obtain ⟨P,hP,hT,hpre⟩ := (Finset.mem_filter.mp ht).2
  refine ⟨t,P,hP,hT,hpre,fun z hz hg => ?_⟩
  have hE : E (t+1) := by
    have e : t+1+n=t+n+1 := by omega
    let R : Chain G (t+1+n) := e ▸ grow P z hg
    have vertex (j) : R.vertex j = (grow P z hg).vertex j := by
      have castv {i l : ℕ} (eq : i=l) (A : Chain G l) (j) : (eq ▸ A : Chain G i).vertex j=A.vertex j := by subst l; rfl
      exact castv e _ _
    refine ⟨R,by rw [vertex]; exact hz,fun i hi => ?_,fun i hi => ?_⟩
    · rw [vertex, show t+1+i=(t+i)+1 by omega]
      exact hT i hi
    · rw [vertex]
      cases i with
      | zero => exact hz
      | succ i => exact hpre i (by omega)
  have := hmax _ (feasible hE)
  simp at this

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem Chain.card_le_of_metricSuffix (P : Chain G n) (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (hn : 2 ≤ n) (N : Finset V)
    (ha : ∀ w ∈ N, G.Adj (P.vertex 0) w) (sat : ∀ w ∈ N, ¬ Good P w)
    {t : ℕ} (hs : P.metricSuffix t) : N.card ≤ (t-1)/2+3 := by
  by_contra! h
  have code := P.suffixCode hc hs
  obtain ⟨_,_,i,hi,he,_⟩ := P.private_of_code hc c h4 hn N ha sat _ h
    (fun i hi => Nat.lt_succ_of_lt (code.1 i hi)) code.2 ⟨(t-1)/2+3,by omega⟩
  exact (code.1 i hi).ne he

noncomputable def coreNeighbors (S : Finset V) (u : S) : Finset V :=
  ((G.induce (S : Set V)).neighborFinset u).map (Function.Embedding.subtype (· ∈ S))

omit [Fintype V] [DecidableEq V] in
theorem coreNeighbors_card (S : Finset V) (u : S) :
    (coreNeighbors (G := G) S u).card = (G.induce (S : Set V)).degree u := by
  simp [coreNeighbors]

omit [Fintype V] [DecidableEq V] in
theorem mem_coreNeighbors {S : Finset V} {u : S} {w : V}
    (h : w ∈ coreNeighbors (G := G) S u) : G.Adj u.val w ∧ w ∈ S := by
  obtain ⟨w',hw,rfl⟩ := Finset.mem_map.mp h
  exact ⟨((G.induce (S : Set V)).mem_neighborFinset _ _).mp hw, w'.property⟩

/-- The reversed path retains the geodesic down to its first neighbor of
the anchor. Every vertex beyond that neighbor lies in the given core. -/
structure RetainsGeodesic {a v : V} (q : G.Walk a v) (S : Finset V)
    {n : ℕ} (P : Chain G n) : Prop where
  suffix : ∀ j ≤ q.length-1, P.reverse.vertex j=q.getVert (q.length-j)
  inside : ∀ i ≤ n, q.length-1 < i → P.reverse.vertex i ∈ S

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem retains_of_forward {a v : V} (q : G.Walk a v) {S : Finset V}
    (P : Chain G n) (t : ℕ) (hlen : n=t+q.length) (hpos : 0<q.length)
    (hsuf : ∀ i, 1 ≤ i → i ≤ q.length → P.vertex (t+i)=q.getVert i)
    (hpre : ∀ i ≤ t, P.vertex i∈S) : RetainsGeodesic q S P := by
  constructor
  · intro j hj
    change P.vertex (n-j)=_
    rw [show n-j=t+(q.length-j) by omega]
    exact hsuf _ (by omega) (by omega)
  · intro i hi hj
    exact hpre (n-i) (by omega)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem RetainsGeodesic.of_grow {a v : V} {q : G.Walk a v} {S : Finset V} {P : Chain G n}
    (h : RetainsGeodesic q S P) (hlen : q.length ≤ n) {Q : Chain G (n+1)}
    (hx : Q.vertex 0∈S) (hQ : ∀ i,Q.vertex (i+1)=P.vertex i) : RetainsGeodesic q S Q := by
  constructor
  · intro j hj
    have h' := h.suffix j hj
    change Q.vertex (n+1-j)=_
    rw [show n+1-j=(n-j)+1 by omega,hQ]
    exact h'
  · intro i hi hj
    change Q.vertex (n+1-i)∈S
    by_cases he : i=n+1
    · simpa [he] using hx
    · rw [show n+1-i=(n-i)+1 by omega,hQ]
      exact h.inside i (by omega) hj

omit [DecidableRel G.Adj] in
theorem exists_seeded_geodesic_tail (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) (a x : S) {v : V} (q : G.Walk a.val v)
    (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length) (hax : G.Adj a.val x.val)
    (hx : x.val ≠ q.getVert 1) :
    ∃ t n, ∃ P : Chain G n, n=t+q.length ∧ P.vertex (t-1)=x.val ∧
      (∀ j ≤ q.length,P.vertex (t+j)=q.getVert j) ∧ (∀ i ≤ t,P.vertex i∈S) ∧
      (∀ z ∈ S, ¬Good P z) ∧ P.metricSuffix t := by
  classical
  let T := Chain.ofGeodesic q hq
  have T0 : T.vertex 0 = a.val := by simp [T,Chain.ofGeodesic]
  have good : Good T x.val := by
    by_contra h
    obtain ⟨j,hj⟩ := blocker T c (by omega) (by rw [T0]; exact hax) h
    let i := 2*j.val+2
    have hix : G.Adj (q.getVert i) x.val := hj
    have hi : i ≤ q.length := by dsimp [i]; have := j.isLt; omega
    have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le _) hi
    rw [Walk.getVert_zero, Nat.sub_zero] at hh
    have ht := hc.dist_triangle (u := a.val) (v := x.val) (w := q.getVert i)
    rw [dist_eq_one_iff_adj.mpr hax,dist_eq_one_iff_adj.mpr hix.symm,hh] at ht
    have hi2 : i=2 := by dsimp [i] at *; omega
    have ha1 := q.adj_getVert_succ (i := 0) (by omega)
    have ha2 := (q.adj_getVert_succ (i := 1) (by omega)).symm
    have hne : a.val ≠ q.getVert i := by intro e; have hz : G.dist a.val (q.getVert i) = 0 := (congrArg (G.dist a.val) e.symm).trans G.dist_self; omega
    exact hx (h4 hne hax hix (by simpa using ha1) (hi2 ▸ ha2))
  let T₀ := grow T x.val good
  obtain ⟨s,P,hPu,hseed,hpre,sat⟩ := longest_seed T₀ S x.property
  let t := s+1
  let L := s+(q.length+1)
  have hL : L = t+q.length := by dsimp [L,t]; omega
  have hsuf (j) (hj : j ≤ q.length) : P.vertex (t+j) = q.getVert j := by
    have h := hseed (j+1) (by omega)
    change P.vertex (s+(j+1)) = q.getVert j at h
    rw [← h,show t+j=s+(j+1) by dsimp [t]; omega]
  have hX : P.vertex (t-1) = x.val := by simpa [t,T₀,grow,Chain.prepend] using hseed 0 (Nat.zero_le _)
  have hsMetric : P.metricSuffix t := by
    intro i hi hin
    have hlast : P.vertex L = v := hL ▸ (hsuf q.length le_rfl).trans q.getVert_length
    have hidx := hsuf (i-t) (by dsimp [t,L] at *; omega)
    rw [Nat.add_sub_of_le hi] at hidx
    rw [show P.vertex (s+(q.length+1)) = v from hlast, hidx]
    have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (i := i-t) (j := q.length)
      (by dsimp [t] at *; omega) le_rfl
    rw [Walk.getVert_length] at hh
    rw [hh]; dsimp [t] at *; omega
  have allCore (i) (hi : i ≤ t) : P.vertex i∈S := by
    by_cases small : i < s
    · exact hpre i small
    rcases (show i=t-1 ∨ i=t by dsimp [t] at *; omega) with h|h
    · exact h ▸ hX ▸ x.property
    · have an : P.vertex t = a.val := by simpa using hsuf 0 (Nat.zero_le _)
      rw [h,an]; exact a.property
  exact ⟨t,L,P,hL,hX,hsuf,allCore,sat,hsMetric⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Every possible even blocking index is near the start when the endpoint
is close to the original anchor and the suffix follows its geodesic. -/
theorem Chain.block_limit (P : Chain G n) (hc : G.Connected) {a v : V} (q : G.Walk a v)
    (hq : q.length = G.dist a v) (t skip r : ℕ) (hlen : n=t+q.length)
    (hs : ∀ j, skip ≤ j → j ≤ q.length → P.vertex (t+j)=q.getVert j)
    (hskip : skip ≤ r+2) (hnear : G.dist a (P.vertex 0) ≤ r) {i} (hi : P.Blocks i) :
    i ≤ t+r+2 := by
  by_cases h : t+skip ≤ i
  · obtain ⟨hn,_,_,hd⟩ := hi
    have hqv := hs (i-t) (by omega) (by omega)
    rw [Nat.add_sub_of_le (by omega : t ≤ i)] at hqv
    have he := dist_getVert_eq_sub_of_le_of_length_eq_dist q hq (Nat.zero_le (i-t)) (by omega)
    rw [Walk.getVert_zero,Nat.sub_zero,←hqv] at he
    have tri := hc.dist_triangle (u := a) (v := P.vertex 0) (w := P.vertex i)
    rw [he] at tri
    omega
  · omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem previous_site (P : Chain G n) (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {t : ℕ} (ht : 3 ≤ t) (hn : 2 ≤ n) (hm : P.metricSuffix t)
    (N : Finset V) (ha : ∀ w ∈ N, G.Adj (P.vertex 0) w)
    (sat : ∀ w ∈ N, ¬Good P w) (hcard : (t-1)/2+3 ≤ N.card) :
    ∃ w ∈ N, G.Adj (P.vertex (2*((t-1)/2))) w := by
  have code := P.suffixCode hc hm
  obtain ⟨w,hw,i,hi,he,hadj,-⟩ := P.private_of_code hc c h4 hn N ha sat _ hcard code.1 code.2
    ⟨(t-1)/2-1,by omega⟩
  have ix : i=2*((t-1)/2) := by
    have := hi.2.2.1; have := hi.2.1
    change (if i<t then i/2-1 else _+_) = (t-1)/2-1 at he
    split_ifs at he <;> omega
  exact ⟨w,hw,ix ▸ hadj⟩

omit [Fintype V] [DecidableRel G.Adj] in
theorem rotate_odd_geodesic_tail (P : Chain G n) (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) (a x : S) {v : V} (q : G.Walk a.val v)
    (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length) (hax : G.Adj a.val x.val)
    {d t : ℕ} (hd : 4 ≤ d) (ht : t=2*d-5) (hL : n=t+q.length)
    (hX : P.vertex (t-1)=x.val) (hsuf : ∀ j ≤ q.length, P.vertex (t+j)=q.getVert j)
    (allCore : ∀ i ≤ t, P.vertex i∈S) (hsMetric : P.metricSuffix t)
    (N : Finset V) (hN : ∀ w ∈ N,G.Adj (P.vertex 0) w) (hin : ∀w∈N,w∈S)
    (hsat : ∀w∈N,¬Good P w) (hdN : d ≤ N.card) :
    ∃ R : Chain G n, R.vertex 0=x.val ∧ RetainsGeodesic q S R ∧
      (∀ i, 1 ≤ i → i ≤ q.length → R.vertex (t+i)=q.getVert i) ∧
      ∀ i, R.Blocks i → i ≤ t+3 := by
  have dEq : (t-1)/2+3=d := by omega
  obtain ⟨w,hw,hadj⟩ := previous_site P hc c h4 (by omega) (by omega) hsMetric N hN hsat (by omega)
  rw [show 2*((t-1)/2)=t-1 by omega,hX] at hadj
  have hnear : G.dist a.val (P.vertex 0) ≤ 3 := by
    have h₁ := hc.dist_triangle (u := x.val) (v := w) (w := P.vertex 0)
    have h₂ := hc.dist_triangle (u := a.val) (v := x.val) (w := P.vertex 0)
    rw [dist_eq_one_iff_adj.mpr hadj,dist_eq_one_iff_adj.mpr (hN _ hw).symm] at h₁
    rw [dist_eq_one_iff_adj.mpr hax] at h₂
    omega
  have limited (i) (hi : P.Blocks i) : i ≤ t+5 :=
    P.block_limit hc q hq t 0 3 hL (fun j _ hj => hsuf j hj) (by omega) hnear hi
  obtain ⟨b,hb,j,hj,hslot,hb2,honly⟩ := P.private_of_code hc c h4 (by omega) N hN hsat
    (fun i => i/2-1) hdN
    (fun i hi => by have := limited i hi; omega)
    (fun i j hi hj he => by have := hi.2.2.1; have := hj.2.2.1; have := hi.2.1; have := hj.2.1; omega)
    ⟨(t+1)/2-1,by omega⟩
  have jEq : j=t+1 := by
    have := hj.2.2.1; have := hj.2.1
    change j/2-1=(t+1)/2-1 at hslot
    omega
  let R := P.rotateAt j (by omega) hj.1 (hN _ hb) hb2 honly
  have rX : R.vertex 0 = x.val := by
    simpa [R,Chain.rotateAt,jEq, show ¬t+1≤0 by omega, show 0≠t by omega,
      show t+1-2=t-1 by omega] using hX
  have fixed (i) (h : j ≤ i) : R.vertex i = P.vertex i := by simp [R,Chain.rotateAt,h]
  have retR : RetainsGeodesic q S R := by
    apply retains_of_forward q R t hL (by omega)
    · intro k hkpos hk
      rw [fixed _ (by omega)]
      exact hsuf k hk
    · intro k hk
      change (if j ≤ k then _ else if k+1=j then _ else _)∈S
      split_ifs
      · omega
      · exact hin b hb
      · exact allCore _ (by omega)
  have suf (i) (hi : 1 ≤ i) (hi' : i ≤ q.length) : R.vertex (t+i) = q.getVert i :=
    (fixed _ (by omega)).trans (hsuf i hi')
  refine ⟨R,rX,retR,suf,fun i hi => ?_⟩
  apply R.block_limit hc q hq t 1 1 hL suf (by omega) _ hi
  rw [rX,dist_eq_one_iff_adj.mpr hax]

/-- Rotation back to the first prescribed neighbor gains one step at a tight
odd tail. If the new length is globally maximal, the new endpoint is a
minimum-degree vertex in the starting color class. -/
theorem geodesic_rotation_witnesses (hc : G.Connected) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a x : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1) {e : ℕ} (he : e ≤ 1)
    (boost : ∀ y : S, c y.val=c a.val → d+e ≤ (G.induce (S : Set V)).degree y) :
    ∃ n, ∃ T : Chain G n, q.length+2*d+e-3 ≤ n+1 ∧ RetainsGeodesic q S T := by
  classical
  obtain ⟨t,L,P,hL,hX,hsuf,allCore,sat,hsMetric⟩ :=
    exists_seeded_geodesic_tail hc c h4 S a x q hq hl hax hx
  let u : S := ⟨P.vertex 0,(allCore 0 (by omega))⟩
  let N := coreNeighbors (G := G) S u
  have hN (w) (hw : w ∈ N) : G.Adj (P.vertex 0) w := (mem_coreNeighbors hw).1
  have hsat (w) (hw : w ∈ N) : ¬Good P w := sat w (mem_coreNeighbors hw).2
  have card := coreNeighbors_card (G := G) S u
  change N.card = _ at card
  have hdN : d ≤ N.card := card ▸ hmin u
  have upper := P.card_le_of_metricSuffix hc c h4 (by omega) N hN hsat hsMetric
  have plen := P.length_le
  change L+1 ≤ G.path at plen
  have retained := retains_of_forward q P t hL (by omega) (fun j _ hj => hsuf j hj) allCore
  by_cases enough : q.length+2*d+e-3 ≤ L+1
  · exact ⟨L,P,enough,retained⟩
  have ht : t=2*d-5 := by
    by_contra h
    have hteven : t=2*d-4 := by omega
    have hcol := P.color_val c t (by omega)
    have anchor : P.vertex t=a.val := by simpa using hsuf 0 (Nat.zero_le _)
    rw [anchor] at hcol
    have sameColor : c u.val = c a.val := by
      apply Fin.ext
      have := (c u.val).isLt
      change (c a.val).val = ((c u.val).val+t)%2 at hcol
      omega
    have hh := boost u sameColor
    omega
  obtain ⟨R,rX,retR,rSuf,Rbound⟩ := rotate_odd_geodesic_tail P hc c h4 S a x q hq hl hax
    (d := d) hd ht hL hX hsuf allCore hsMetric N hN (fun _ hz => (mem_coreNeighbors hz).2) hsat hdN
  let B := coreNeighbors (G := G) S x
  have hBcard := coreNeighbors_card (G := G) S x
  change B.card = _ at hBcard
  obtain ⟨Q,hQS,hQR⟩ := R.extendByCode hc c h4 (by omega) (S : Set V) B
    (show d-1 < B.card by have := hmin x; omega)
    (fun z hz => ⟨rX ▸ (mem_coreNeighbors hz).1,(mem_coreNeighbors hz).2⟩)
    (fun i => i/2-1)
    (fun i hi => by have := Rbound i hi; omega)
    (fun i j hi hj he => by have := hi.2.2.1; have := hj.2.2.1; have := hi.2.1; have := hj.2.1; omega)
  have retQ := retR.of_grow (by omega) hQS hQR
  by_cases doneQ : q.length+2*d+e-3 ≤ L+1+1
  · exact ⟨L+1,Q,doneQ,retQ⟩
  let y : S := ⟨Q.vertex 0,hQS⟩
  have hxy : G.Adj x.val y.val := by
    have h := (Q.edges (i := 1) (j := 0) (by omega) (by omega)).2 (Or.inr rfl)
    rw [hQR 0,rX] at h
    exact h
  have hcol : c y.val = c a.val := by
    apply Fin.ext
    have := Fin.val_ne_of_ne (c.valid hxy)
    have := Fin.val_ne_of_ne (c.valid hax)
    have := (c a.val).isLt; have := (c x.val).isLt; have := (c y.val).isLt
    omega
  have ydist : G.dist a.val y.val ≤ 2 := by
    have h := hc.dist_triangle (u := a.val) (v := x.val) (w := y.val)
    rwa [dist_eq_one_iff_adj.mpr hax,dist_eq_one_iff_adj.mpr hxy] at h
  have Qsuf (i) (hi : 1 ≤ i) (hi' : i ≤ q.length) : Q.vertex (t+1+i)=q.getVert i := by
    rw [show t+1+i=(t+i)+1 by omega,hQR]; exact rSuf i hi hi'
  have Qbound (i) (hi : Q.Blocks i) : i ≤ t+5 :=
    Q.block_limit hc q hq (t+1) 1 2 (by omega) Qsuf (by omega) ydist hi
  let Y := coreNeighbors (G := G) S y
  have hYcard := coreNeighbors_card (G := G) S y
  change Y.card = _ at hYcard
  have hh := boost y hcol
  obtain ⟨Z,hZS,hZQ⟩ := Q.extendByCode hc c h4 (by omega) (S : Set V) Y
    (show d < Y.card by omega) (fun z h => mem_coreNeighbors h) (fun i => i/2-1)
    (fun i hi => by have := Qbound i hi; omega)
    (fun i j hi hj he => by have := hi.2.2.1; have := hj.2.2.1; have := hi.2.1; have := hj.2.1; omega)
  exact ⟨L+1+1,Z,by omega,retQ.of_grow (by omega) hZS hZQ⟩

theorem exists_rotated_core_path_aux (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length)
    {e : ℕ} (he : e ≤ 1) (boost : ∀ y : S, c y.val=c a.val → d+e ≤ (G.induce (S : Set V)).degree y) :
    ∃ n, ∃ T : Chain G n, q.length+2*d+e-3 ≤ n+1 ∧ RetainsGeodesic q S T := by
  classical
  let H := G.induce (S : Set V)
  have hex : ∃ x ∈ H.neighborFinset a, (x : S).val ≠ q.getVert 1 := by
    by_contra! h
    have card : (H.neighborFinset a).card ≤ 1 := Finset.card_le_one.mpr
      (fun x hx y hy => Subtype.ext ((h x hx).trans (h y hy).symm))
    rw [H.card_neighborFinset_eq_degree] at card
    have hbase : d ≤ H.degree a := hmin a
    omega
  obtain ⟨x,hx,hx'⟩ := hex
  exact geodesic_rotation_witnesses hc c h4 S hd hmin a x q hq hl ((H.mem_neighborFinset _ _).mp hx) hx' he boost

theorem exists_rotated_core_path (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length) :
    ∃ n, ∃ T : Chain G n, q.length+2*d-3 ≤ n+1 ∧ RetainsGeodesic q S T :=
  exists_rotated_core_path_aux hc c h4 S hd hmin a q hq hl (e := 0) (by decide) (fun y _ => hmin y)

theorem exists_rotated_high_core_path (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length)
    (boost : ∀ y : S, c y.val=c a.val → d+1 ≤ (G.induce (S : Set V)).degree y) :
    ∃ n, ∃ T : Chain G n, q.length+2*d-2 ≤ n+1 ∧ RetainsGeodesic q S T := by
  obtain ⟨n,T,h,hT⟩ := exists_rotated_core_path_aux hc c h4 S hd hmin a q hq hl (e := 1) (by decide) boost
  exact ⟨n,T,by omega,hT⟩

/-- A geodesic of length at least five from the core always gains at least
twice its minimum degree minus three vertices. -/
theorem geodesic_add_twice_degree_le_path_add_three (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V) {d : ℕ} (hd : 4 ≤ d)
    (hmin : ∀ u : S, d ≤ (G.induce (S : Set V)).degree u) (a : S) {v : V}
    (q : G.Walk a.val v) (hq : q.length = G.dist a.val v) (hl : 5 ≤ q.length) :
    q.length+2*d ≤ G.path+3 ∧ (G.path ≤ q.length+2*d-3 →
      ∃ y : S, c y.val = c a.val ∧ (G.induce (S : Set V)).degree y ≤ d) := by
  classical
  constructor
  · obtain ⟨n,T,h,_⟩ := exists_rotated_core_path hc c h4 S hd hmin a q hq hl
    have := T.length_le
    omega
  · intro hshort
    by_contra! boost
    obtain ⟨n,T,h,_⟩ := exists_rotated_high_core_path hc c h4 S hd hmin a q hq hl boost
    have := T.length_le
    omega

/-- Every even density threshold gives the conjectured bound within one
vertex by rotating a path grown from its dense core. -/
theorem radius_add_even_density_le_path_add_one [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) {m : ℕ} (hm : 3 ≤ m)
    (hdeg : (2*m)*Fintype.card V ≤ ∑ v, G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat+2*m ≤ G.path+1 := by
  obtain ⟨S,hS,hmin⟩ := exists_degree_core G (k := 2*m) (by omega) hdeg
  obtain ⟨a,ha⟩ := hS
  let A : S := ⟨a,ha⟩
  obtain ⟨c⟩ := hb
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc A.val
  have h := (geodesic_add_twice_degree_le_path_add_three hc c h4 S (d := m+1) (by omega)
    (fun u => by have := hmin u; omega) A q hq (by omega)).1
  omega

/-- An asymmetric minimum degree at an odd density threshold rules out
the equality case by taking the initial vertex on the higher-degree side. -/
theorem radius_add_odd_density_le_path_add_one [Nonempty V] (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) {m : ℕ} (hm : 3 ≤ m)
    (hdeg : (2*m+1)*Fintype.card V ≤ ∑ v, G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat+(2*m+1) ≤ G.path+1 := by
  classical
  obtain ⟨col,S,hS,hmin⟩ := exists_odd_degree_core c (by omega : 0 < m) hdeg
  let H := G.induce (S : Set V)
  have base (u : S) : m+1 ≤ H.degree u := (Nat.le_add_right _ _).trans (hmin u)
  have high : ∃ a : S, c a.val=col := by
    obtain ⟨x,hx⟩ := hS
    let b : S := ⟨x,hx⟩
    by_cases hb : c b.val=col
    · exact ⟨b,hb⟩
    have bh := base b
    obtain ⟨a,ha⟩ := (H.degree_pos_iff_exists_adj b).mp (by omega)
    refine ⟨a,Fin.ext ?_⟩
    have := Fin.val_ne_of_ne (c.valid (show G.Adj b.val a.val from ha))
    have := Fin.val_ne_of_ne hb
    have := (c b.val).isLt; have := (c a.val).isLt; have := col.isLt
    omega
  obtain ⟨a,ha⟩ := high
  obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a.val
  have h := geodesic_add_twice_degree_le_path_add_three hc c h4 S (d := m+1) (by omega)
    base a q hq (by omega)
  by_contra! hshort
  obtain ⟨y,hy,hlow⟩ := h.2 (by omega)
  have hh := hmin y
  rw [if_pos (hy.trans ha)] at hh
  omega

/-- The floored conjecture is within one vertex for all connected bipartite
graphs without a four-cycle when the floor is even, at every radius. -/
theorem radius_add_floor_le_path_add_one_of_bipartite_even [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) (he : ⌊l G⌋₊%2=0) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path+1 := by
  by_cases hr : G.radius.toNat ≤ 6
  · have := radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr
    omega
  by_cases hm : 3 ≤ ⌊l G⌋₊/2
  · have eq : 2*(⌊l G⌋₊/2)=⌊l G⌋₊ := by omega
    have hdeg := sum_degree_ge_of_le_l (G := G) (k := ⌊l G⌋₊)
      (Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)))
    have := radius_add_even_density_le_path_add_one hc hb h4 hm (by rwa [eq]) (by omega)
    omega
  · have := chung_bound_nat G hc
    omega



/-- For arbitrary radius and degrees, a connected bipartite graph without a
four-cycle is within one vertex of the requested floored inequality. -/
theorem radius_add_floor_le_path_add_one_of_bipartite [Nonempty V] (hc : G.Connected)
    (hb : G.IsBipartite) (h4 : NoFourCycle G) : G.radius.toNat+⌊l G⌋₊ ≤ G.path+1 := by
  by_cases even : ⌊l G⌋₊%2=0
  · exact radius_add_floor_le_path_add_one_of_bipartite_even hc hb h4 even
  by_cases hr : G.radius.toNat ≤ 6
  · have := radius_add_floor_le_path_of_bipartite_radius_le_six hc hb h4 hr
    omega
  by_cases hm : 3 ≤ ⌊l G⌋₊/2
  · have eq : 2*(⌊l G⌋₊/2)+1=⌊l G⌋₊ := by omega
    have hdeg := sum_degree_ge_of_le_l (G := G) (k := ⌊l G⌋₊)
      (Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v))) (Nat.cast_nonneg _)))
    obtain ⟨c⟩ := hb
    have := radius_add_odd_density_le_path_add_one hc c h4 hm (by rwa [eq]) (by omega)
    omega
  · have := chung_bound_nat G hc
    omega

end Wall133
