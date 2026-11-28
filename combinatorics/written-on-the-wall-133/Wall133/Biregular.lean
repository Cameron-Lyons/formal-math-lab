module

public import Wall133.BipartiteDensity

@[expose] public section

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

def Chain.ofGeodesic {a b : V} (p : G.Walk a b)
    (hp : p.length = G.dist a b) : Chain G p.length where
  vertex := p.getVert
  inj := by
    intro i j hi hj h
    rcases le_total i j with hij | hji
    · have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp hij hj
      rw [h, G.dist_self] at hh
      omega
    · have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp hji hi
      rw [h, G.dist_self] at hh
      omega
  edges hi hj := adj_getVert_iff_consecutive_of_length_eq_dist p hp hi hj

theorem Chain.dist_le_sub {n : ℕ} (P : Chain G n) (hc : G.Connected)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    G.dist (P.vertex i) (P.vertex j) ≤ j-i := by
  induction j with
  | zero =>
    obtain rfl : i = 0 := by omega
    simp
  | succ j ih =>
    by_cases h : i ≤ j
    · have ht := hc.dist_triangle (u := P.vertex i) (v := P.vertex j) (w := P.vertex (j+1))
      rw [dist_eq_one_iff_adj.mpr ((P.edges (by omega) hj).2 (Or.inl rfl))] at ht
      have := ih h (by omega)
      omega
    · obtain rfl : i = j+1 := by omega
      simp

def Chain.Blocks {n : ℕ} (P : Chain G n) (i : ℕ) : Prop :=
  i ≤ n ∧ i ≠ 0 ∧ i % 2 = 0 ∧ G.dist (P.vertex 0) (P.vertex i) ≤ 2

/-- If all possible blocking sites can be indexed by fewer positions than the
degree of the active endpoint, some neighbor extends the induced path. -/
theorem Chain.extendByCode {n m : ℕ}
    (P : Chain G n) (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hn : 2 ≤ n) (S : Set V) (N : Finset V) (hd : m < N.card)
    (hN : ∀ z ∈ N, G.Adj (P.vertex 0) z ∧ z ∈ S)
    (code : ℕ → ℕ) (bound : ∀ i, P.Blocks i → code i < m)
    (inj : ∀ i j, P.Blocks i → P.Blocks j → code i = code j → i = j) :
    ∃ Q : Chain G (n+1), Q.vertex 0 ∈ S ∧ ∀ i, Q.vertex (i+1) = P.vertex i := by
  classical
  by_contra h
  have block (z : ↥N) : ∃ j, P.Blocks j ∧ G.Adj (P.vertex j) z := by
    have hz := (hN _ z.property).1
    have hex : ∃ i ≤ n, i ≠ 0 ∧ G.Adj (P.vertex i) z := by
      by_contra! hbad
      have fresh (i : ℕ) (hi : i ≤ n) : z.val ≠ P.vertex i := by
        intro he
        rw [he] at hz
        have h1 := (P.edges (Nat.zero_le _) hi).1 hz
        obtain rfl : i = 1 := by omega
        apply hbad 2 hn (by decide)
        rw [he]
        exact (P.edges hn hi).2 (by decide)
      exact h ⟨P.prepend z.val hz.symm fresh (fun i hi hn' ha => hbad i hi hn' ha.symm),
        (hN _ z.property).2, fun _ => rfl⟩
    obtain ⟨j, hj, hzj, ha⟩ := hex
    refine ⟨j, ⟨hj, hzj, P.even_of_common c hj hz ha, ?_⟩, ha⟩
    have ht := hc.dist_triangle (u := P.vertex 0) (v := z.val) (w := P.vertex j)
    rwa [dist_eq_one_iff_adj.mpr hz, dist_eq_one_iff_adj.mpr ha.symm] at ht
  choose idx hi ha using block
  let f (z : ↥N) : Fin m := ⟨code (idx z), bound _ (hi z)⟩
  have fi : Function.Injective f := by
    intro x y he
    have eq := inj _ _ (hi x) (hi y) (congrArg Fin.val he)
    apply Subtype.ext
    apply h4 (x := P.vertex 0) (y := P.vertex (idx x))
    · intro he'
      exact (hi x).2.1 ((P.inj (Nat.zero_le _) (hi x).1 he').symm)
    · exact (hN _ x.property).1
    · exact ha x
    · exact (hN _ y.property).1
    · rw [eq]; exact ha y
  have hh := Fintype.card_le_of_injective f fi
  simp only [Fintype.card_fin, Fintype.card_coe] at hh
  omega

variable [Fintype V] [DecidableRel G.Adj]

private def HasNeighbors (S : Set V) (d : ℕ) : Prop :=
  ∀ v ∈ S, ∃ N : Finset V, d ≤ N.card ∧ ∀ z ∈ N, G.Adj v z ∧ z ∈ S

private theorem hasNeighbors_univ {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) :
    HasNeighbors (G := G) Set.univ d := fun v _ =>
  ⟨G.neighborFinset v, hmin v, fun _ h => ⟨(G.mem_neighborFinset _ _).mp h, Set.mem_univ _⟩⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem extend_tail_from {w a : V} (p : G.Walk w a) (hp : p.length = G.dist w a)
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (S : Set V) {d s : ℕ} (hd : 3 ≤ d)
    (hmin : HasNeighbors (G := G) S d) (hD : 5 ≤ p.length)
    (start : ∃ P : Chain G (p.length+s), P.vertex 0 ∈ S ∧ ∀ i ≤ p.length, P.vertex (s+i) = p.getVert i)
    (j : ℕ) (hsj : s ≤ j) (hj : j ≤ 2*d-5) :
    ∃ P : Chain G (p.length+j), P.vertex 0 ∈ S ∧ ∀ i ≤ p.length, P.vertex (j+i) = p.getVert i := by
  induction j, hsj using Nat.le_induction with
  | base => exact start
  | succ j _ ih =>
    obtain ⟨P, hPS, hP⟩ := ih (by omega)
    let D := p.length
    let A := G.dist (P.vertex 0) a
    let b := j+D-(A+2)
    let offset := (j-1)/2
    let code (i : ℕ) := if i < j then i/2-1 else offset+(i-b)/2
    have window (i : ℕ) (h : P.Blocks i) (hij : j ≤ i) : b ≤ i ∧ i ≤ b+4 := by
      obtain ⟨hn, -, -, hdist⟩ := h
      have hei : P.vertex i = p.getVert (i-j) := by
        simpa only [Nat.add_sub_of_le hij] using hP (i-j) (by omega)
      have he := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp
        (i := i-j) (j := p.length) (by omega) le_rfl
      simp only [Walk.getVert_length, ← hei] at he
      have hh₁ := hc.dist_triangle (u := P.vertex 0) (v := P.vertex i) (w := a)
      have hh₂ := hc.dist_triangle (u := P.vertex i) (v := P.vertex 0) (w := a)
      rw [G.dist_comm (u := P.vertex i) (v := P.vertex 0)] at hh₂
      dsimp [b, A, D]
      omega
    have first (i : ℕ) (h : P.Blocks i) (hz : j = 0) : i ≤ 2 := by
      obtain ⟨hn, -, -, hdist⟩ := h
      have he := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp (i := 0) (j := i)
        (Nat.zero_le _) (by omega)
      have h₀ := hP 0 (Nat.zero_le _)
      have hi := hP i (by omega)
      rw [show j+i = i by omega] at hi
      rw [show j+0 = 0 by omega] at h₀
      rw [← hi, ← h₀, Nat.sub_zero] at he
      omega
    have bounds (i : ℕ) (h : P.Blocks i) : code i < d-1 := by
      have hp' := h.2.1
      have he := h.2.2.1
      dsimp [code, offset]
      split_ifs with hh
      · omega
      · have hw := window i h (by omega)
        by_cases hz : j = 0
        · have hi := first i h hz
          omega
        · omega
    have injective (i k : ℕ) (hi : P.Blocks i) (hk : P.Blocks k) (eq : code i = code k) :
        i = k := by
      have he₁ := hi.2.2.1
      have he₂ := hk.2.2.1
      have hp₁ := hi.2.1
      have hp₂ := hk.2.1
      dsimp [code, offset] at eq
      split_ifs at eq with hh hh' hh'
      · omega
      · omega
      · omega
      · have := window i hi (by omega)
        have := window k hk (by omega)
        omega
    obtain ⟨N, hNcard, hN⟩ := hmin _ hPS
    obtain ⟨Q, hQS, hQ⟩ := P.extendByCode hc c h4 (by omega) S N
      (by omega : d-1 < N.card) hN code bounds injective
    exact ⟨Q, hQS, fun i hi => by
      simpa only [Nat.succ_add] using (hQ (j+i)).trans (hP i hi)⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- A blocker on the original geodesic lies near the second endpoint,
while a blocker on the added tail lies far along it. These two index
ranges permit as many second-end extensions as the geodesic length allows. -/
private theorem extend_other_end_from {w a : V} (p : G.Walk w a) (hp : p.length = G.dist w a)
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (S : Set V) (haS : a ∈ S) {d : ℕ} (hd : 3 ≤ d)
    (hmin : HasNeighbors (G := G) S d) (hD : 5 ≤ p.length)
    (tail : ∃ P : Chain G (p.length+(2*d-5)), P.vertex 0 ∈ S ∧
      ∀ i ≤ p.length, P.vertex ((2*d-5)+i) = p.getVert i)
    (j : ℕ) (hj : j ≤ d-1)
    (hfar : 3*j ≤ p.length+1 ∨ j=3 ∧ 7 ≤ p.length ∧
      ∀ v ∈ S, c v = c a → ∃ N : Finset V, d+1 ≤ N.card ∧ ∀ z ∈ N, G.Adj v z ∧ z ∈ S) :
    ∃ P : Chain G ((p.length + (2*d-5))+j), P.vertex 0 ∈ S ∧
      ∀ i ≤ p.length, P.vertex (j+i) = p.getVert (p.length-i) := by
  let t := 2*d-5
  let D := p.length
  induction j with
  | zero =>
    obtain ⟨P, _, hP⟩ := tail
    refine ⟨P.reverse, ?_, fun i hi => ?_⟩
    · change P.vertex (p.length+t-0) ∈ S
      have he := hP p.length le_rfl
      rw [Nat.add_comm t p.length, Walk.getVert_length] at he
      simpa only [Nat.sub_zero, he] using haS
    change P.vertex (p.length + t - (0+i)) = _
    rw [show p.length + t - (0+i) = t+(p.length-i) by omega]
    exact hP _ (Nat.sub_le _ _)
  | succ j ih =>
    obtain ⟨P, hPS, hP⟩ := ih (by omega) (Or.inl (by rcases hfar with h | ⟨h,hn,_⟩ <;> omega))
    have hleft : P.vertex j = a := by simpa using hP 0 (Nat.zero_le _)
    have hright : P.vertex (j+D) = w := by simpa [D] using hP p.length le_rfl
    have hdist : G.dist a (P.vertex 0) ≤ j := by
      have hh := P.dist_le_sub hc (i := 0) (j := j) (Nat.zero_le _) (by omega)
      rw [hleft, G.dist_comm] at hh
      simpa using hh
    have ranges (i : ℕ) (h : P.Blocks i) : i ≤ 2*j+2 ∨ 2*D-2 ≤ i := by
      obtain ⟨hn, -, -, hsite⟩ := h
      have ha := hc.dist_triangle (u := a) (v := P.vertex 0) (w := P.vertex i)
      by_cases hge : i ≤ j+D
      · left
        by_cases hij : j ≤ i
        · have he : P.vertex i = p.getVert (p.length-(i-j)) := by
            simpa only [Nat.add_sub_of_le hij] using hP (i-j) (by dsimp [D] at hge; omega)
          have hh := dist_getVert_eq_sub_of_le_of_length_eq_dist p hp
            (i := p.length-(i-j)) (j := p.length) (Nat.sub_le _ _) le_rfl
          rw [Walk.getVert_length, ← he, G.dist_comm] at hh
          dsimp [D] at hge
          omega
        · omega
      · right
        have dfar := P.dist_le_sub hc (i := j+D) (j := i) (by omega) hn
        rw [hright, G.dist_comm] at dfar
        have hf := hc.dist_triangle (u := a) (v := P.vertex i) (w := w)
        rw [G.dist_comm (u := a) (v := w), ← hp] at hf
        dsimp [D] at *
        omega
    let code (i : ℕ) := if i ≤ 2*j+2 then i/2-1 else j+1+(i-(2*D-2))/2
    let extra := if 3*(j+1) ≤ p.length+1 then 0 else 1
    have room : 3*(j+1) ≤ p.length+1+extra := by
      dsimp [extra]; split_ifs <;> rcases hfar with h | ⟨h,hn,_⟩ <;> omega
    have bounds (i : ℕ) (h : P.Blocks i) : code i < d-1+extra := by
      have hn := h.1
      have he := h.2.2.1
      have hpos := h.2.1
      have hr := ranges i h
      dsimp [code, D] at *
      split_ifs <;> omega
    have injective (i k : ℕ) (hi : P.Blocks i) (hk : P.Blocks k) (eq : code i = code k) :
        i = k := by
      have he₁ := hi.2.2.1
      have he₂ := hk.2.2.1
      have hp₁ := hi.2.1
      have hp₂ := hk.2.1
      have := ranges i hi
      have := ranges k hk
      dsimp [code] at eq
      split_ifs at eq <;> omega
    have budget : ∃ N : Finset V, d+extra ≤ N.card ∧ ∀ z ∈ N, G.Adj (P.vertex 0) z ∧ z ∈ S := by
      dsimp [extra]; split_ifs with h
      · exact hmin _ hPS
      · obtain ⟨hj',_,hh⟩ := hfar.resolve_left h
        apply hh _ hPS
        have hv := P.color_val c j (by omega)
        rw [hleft] at hv
        have := (c (P.vertex 0)).isLt
        exact Fin.ext (by omega)
    obtain ⟨N, hNcard, hN⟩ := budget
    obtain ⟨Q, hQS, hQ⟩ := P.extendByCode hc c h4 (by omega) S N
      (by omega : d-1+extra < N.card) hN code bounds injective
    exact ⟨Q, hQS, fun i hi => by
      simpa only [Nat.succ_add] using (hQ (j+i)).trans (hP i hi)⟩

omit [Fintype V] [DecidableRel G.Adj] in
private theorem extend_other_end {w a : V} (p : G.Walk w a) (hp : p.length = G.dist w a)
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (S : Set V) (hw : w ∈ S) (haS : a ∈ S) {d : ℕ} (hd : 3 ≤ d)
    (hmin : HasNeighbors (G := G) S d) (hD : 5 ≤ p.length)
    (j : ℕ) (hj : j ≤ d-1) (hfar : 3*j ≤ p.length+1) :
    ∃ P : Chain G ((p.length + (2*d-5))+j), P.vertex 0 ∈ S ∧
      ∀ i ≤ p.length, P.vertex (j+i) = p.getVert (p.length-i) := by
  have initial : ∃ P : Chain G (p.length+0), P.vertex 0 ∈ S ∧
      ∀ i ≤ p.length, P.vertex (0+i) = p.getVert i := by
    refine ⟨Chain.ofGeodesic p hp, ?_,fun i _ => by simp [Chain.ofGeodesic]⟩
    simpa [Chain.ofGeodesic] using hw
  have tail := extend_tail_from p hp hc c h4 S hd hmin hD initial (2*d-5) (Nat.zero_le _) le_rfl
  exact extend_other_end_from p hp hc c h4 S haS hd hmin hD tail j hj (Or.inl hfar)

variable [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
private theorem hasNeighbors_of_inner_degree (S : Finset V) {d : ℕ}
    (hmin : ∀ v : S, d ≤ (G.induce (S : Set V)).degree v) :
    HasNeighbors (G := G) (S : Set V) d := by
  classical
  intro v hv
  let u : S := ⟨v, hv⟩
  let H := G.induce (S : Set V)
  let N := (H.neighborFinset u).map (Function.Embedding.subtype (· ∈ S))
  refine ⟨N, ?_, ?_⟩
  · simpa only [N, Finset.card_map, H.card_neighborFinset_eq_degree] using hmin u
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := Finset.mem_map.mp hz
    exact ⟨(H.mem_neighborFinset _ _).mp hz', z'.property⟩

/-- Once the end of an induced extension has reached a dense subgraph, the
remaining extension can be grown there. The geodesic measures the distance
before the first extension; its starting vertex may be outside the subgraph. -/
theorem path_bound_of_core_return {w a : V} (p : G.Walk w a) (hp : p.length = G.dist w a)
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V)
    (ha : a ∈ S) {d s : ℕ} (hd : 3 ≤ d) (hmin : ∀ v : S, d ≤ (G.induce (S : Set V)).degree v)
    (hD : 5 ≤ p.length) (P : Chain G (p.length+s)) (hP : P.vertex 0 ∈ S)
    (hg : ∀ i ≤ p.length, P.vertex (s+i) = p.getVert i) (hs : s ≤ 2*d-5)
    {j : ℕ} (hj : j ≤ d-1) (hfar : 3*j ≤ p.length+1) :
    p.length + 2*d + j ≤ G.path+4 := by
  have hN := hasNeighbors_of_inner_degree (G := G) S hmin
  have tail := extend_tail_from p hp hc c h4 (S : Set V) hd hN hD ⟨P,hP,hg⟩ (2*d-5) hs le_rfl
  obtain ⟨T,_,_⟩ := extend_other_end_from p hp hc c h4 (S : Set V) ha hd hN hD tail j hj (Or.inl hfar)
  have := T.length_le
  omega

/-- With an extra neighbor in the color class of the second anchor, the
third extension at that end works even for a seven-edge geodesic. -/
theorem path_bound_of_high_core_return {w a : V} (p : G.Walk w a) (hp : p.length = G.dist w a)
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (S : Finset V)
    (ha : a ∈ S) {d s : ℕ} (hd : 4 ≤ d) (hmin : ∀ v : S, d ≤ (G.induce (S : Set V)).degree v)
    (hhigh : ∀ v : S, c v.val=c a → d+1 ≤ (G.induce (S : Set V)).degree v)
    (hD : 7 ≤ p.length) (P : Chain G (p.length+s)) (hP : P.vertex 0 ∈ S)
    (hg : ∀ i ≤ p.length, P.vertex (s+i) = p.getVert i) (hs : s ≤ 2*d-5) :
    p.length + 2*d + 3 ≤ G.path+4 := by
  classical
  have hN := hasNeighbors_of_inner_degree (G := G) S hmin
  have tail := extend_tail_from p hp hc c h4 (S : Set V) (by omega : 3 ≤ d) hN (by omega)
    ⟨P,hP,hg⟩ (2*d-5) hs le_rfl
  have high : ∀ v ∈ (S : Set V), c v=c a →
      ∃ N : Finset V, d+1 ≤ N.card ∧ ∀ z ∈ N, G.Adj v z ∧ z ∈ (S : Set V) := by
    intro v hv hc'
    let u : S := ⟨v,hv⟩
    let H := G.induce (S : Set V)
    let N := (H.neighborFinset u).map (Function.Embedding.subtype (· ∈ S))
    refine ⟨N,?_,?_⟩
    · simpa only [N,Finset.card_map,H.card_neighborFinset_eq_degree] using hhigh u hc'
    · intro z hz
      obtain ⟨z,hz',rfl⟩ := Finset.mem_map.mp hz
      exact ⟨(H.mem_neighborFinset u z).mp hz',z.property⟩
  obtain ⟨T,_,_⟩ := extend_other_end_from p hp hc c h4 (S : Set V) ha (by omega : 3 ≤ d) hN
    (by omega) tail 3 (by omega) (Or.inr ⟨rfl,hD,high⟩)
  have := T.length_le
  omega

/-- Two vertices of the same dense induced subgraph can anchor opposite ends
of an ambient geodesic. The induced subgraph itself may be disconnected. -/
theorem distance_add_twice_core_degree_add_tail_le_path_add_four
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) {d : ℕ} (hd : 3 ≤ d)
    (hmin : ∀ v : S, d ≤ (G.induce (S : Set V)).degree v) (hfar : 5 ≤ G.dist x y)
    {b : ℕ} (hbdeg : b ≤ d-1) (hbdist : 3*b ≤ G.dist x y+1) :
    G.dist x y + 2*d + b ≤ path G + 4 := by
  classical
  obtain ⟨c⟩ := hb
  have eligible := hasNeighbors_of_inner_degree (G := G) S hmin
  obtain ⟨p, _, hp⟩ := hc.exists_path_of_dist x y
  obtain ⟨P, _, _⟩ := extend_other_end p hp hc c h4 (S : Set V) hx hy hd eligible
    (by omega) b hbdeg (by omega)
  have := P.length_le
  omega

/-- The first geodesic may join the two ends of a diameter. -/
theorem diam_add_twice_min_degree_add_tail_le_path_add_four [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ v, d ≤ G.degree v) (hD : 5 ≤ G.diam)
    {b : ℕ} (hbdeg : b ≤ d-1) (hbdiam : 3*b ≤ G.diam+1) :
    G.diam + 2*d + b ≤ path G + 4 := by
  obtain ⟨c⟩ := hb
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  obtain ⟨p, _, hp⟩ := hc.exists_path_of_dist x y
  obtain ⟨P, _, _⟩ := extend_other_end p hp hc c h4 Set.univ (Set.mem_univ _) (Set.mem_univ _)
    hd (hasNeighbors_univ hmin) (by omega) b hbdeg (by omega)
  have := P.length_le
  omega

/-- Starting with a geodesic of length at least the radius, grow an induced
tail of length `2*d-5` from one end and a tail of length `b` from the other. -/
theorem radius_add_twice_min_degree_add_tail_le_path_add_four [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ v, d ≤ G.degree v) (hr : 5 ≤ G.radius.toNat)
    {b : ℕ} (hbdeg : b ≤ d-1) (hbrad : 3*b ≤ G.radius.toNat+1) :
    G.radius.toNat + 2*d + b ≤ path G + 4 := by
  have hdr : G.radius.toNat ≤ G.diam :=
    ENat.toNat_le_toNat G.radius_le_ediam (G.connected_iff_ediam_ne_top.mp hc)
  have := diam_add_twice_min_degree_add_tail_le_path_add_four hc hb h4 hd hmin (by omega)
    hbdeg (by omega)
  omega

/-- For radius at least five, extending both ends of a geodesic gains
twice the minimum degree minus two vertices over the radius. -/
theorem radius_add_twice_min_degree_le_path_add_two [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ v, d ≤ G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat + 2*d ≤ path G + 2 := by
  have := radius_add_twice_min_degree_add_tail_le_path_add_four hc hb h4 hd hmin hr
    (b := 2) (by omega) (by omega)
  omega

/-- The minimum-degree criterion for the conjecture holds at every radius. -/
theorem radius_add_floor_le_path_of_twice_min_degree [Nontrivial V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) (hk : ⌊l G⌋₊+2 ≤ 2*d) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  by_cases hr : G.radius.toNat ≤ 4
  · exact radius_add_floor_le_path_of_bipartite_radius_le_four hc hb h4 hr
  by_cases hd : 3 ≤ d
  · have := radius_add_twice_min_degree_le_path_add_two hc hb h4 hd hmin (by omega)
    omega
  · have := chung_bound_nat G hc
    omega

/-- From radius eight on, the minimum-degree criterion gains another vertex. -/
theorem radius_add_floor_le_path_of_twice_min_degree_radius_eight [Nonempty V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) (hk : ⌊l G⌋₊+1 ≤ 2*d)
    (hr : 8 ≤ G.radius.toNat) : G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  by_cases hd : 4 ≤ d
  · have := radius_add_twice_min_degree_add_tail_le_path_add_four hc hb h4 (by omega : 3 ≤ d)
      hmin (by omega) (b := 3) (by omega) (by omega)
    omega
  · have := chung_bound_nat G hc
    omega

/-- If some vertex has eccentricity larger than the radius, the diameter
gives one more vertex in the odd minimum-degree band at every radius. -/
theorem radius_add_floor_le_path_of_twice_min_degree_radius_lt_diam [Nontrivial V]
    (hc : G.Connected) (hb : G.IsBipartite) (h4 : NoFourCycle G)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) (hk : ⌊l G⌋₊+1 ≤ 2*d)
    (hgap : G.radius.toNat < G.diam) : G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  by_cases hr : G.radius.toNat ≤ 4
  · exact radius_add_floor_le_path_of_bipartite_radius_le_four hc hb h4 hr
  by_cases hd : 3 ≤ d
  · have := diam_add_twice_min_degree_add_tail_le_path_add_four hc hb h4 hd hmin (by omega)
      (b := 2) (by omega) (by omega)
    omega
  · have := chung_bound_nat G hc
    omega

omit [DecidableEq V] in
private theorem biregular_degree_bounds [Nonempty V] (c : G.Coloring (Fin 2)) (a : V)
    {d M k : ℕ} (horder : d ≤ M) (hv : ∀ v, G.degree v = if c v = c a then M else d)
    (hk : 0 < k) (hdeg : k * Fintype.card V ≤ ∑ v, G.degree v) : k < 2*d ∧ k ≤ M := by
  classical
  let A := Finset.univ.filter (fun v : V => c v = c a)
  let B := Finset.univ.filter (fun v : V => c v ≠ c a)
  have hb : G.IsBipartiteWith (A : Set V) (B : Set V) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro v ha hb
      exact (Finset.mem_filter.mp hb).2 ((Finset.mem_filter.mp ha).2)
    · intro v w hadj
      have he := Fin.val_ne_of_ne (c.valid hadj)
      simp only [A, B, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases ha : c v = c a
      · exact Or.inl ⟨ha, fun hh => c.valid hadj (ha.trans hh.symm)⟩
      · right
        refine ⟨ha, Fin.ext ?_⟩
        have := (c a).isLt
        have := (c v).isLt
        have := (c w).isLt
        have := Fin.val_ne_of_ne ha
        omega
  have high : ∑ v ∈ A, G.degree v = A.card * M := by
    rw [← Nat.nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl (fun v hh => by simp [hv v, (Finset.mem_filter.mp hh).2])
  have low : ∑ v ∈ B, G.degree v = B.card * d := by
    rw [← Nat.nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl (fun v hh => by simp [hv v, (Finset.mem_filter.mp hh).2])
  have balance := isBipartiteWith_sum_degrees_eq hb
  rw [high, low] at balance
  have htotal : ∑ v, G.degree v = 2 * (B.card*d) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : V => c v = c a)]
    change (∑ v ∈ A, G.degree v) + (∑ v ∈ B, G.degree v) = _
    rw [high, low, balance, two_mul]
  have hn : A.card + B.card = Fintype.card V := by
    simpa [A, B] using Finset.univ.card_filter_add_card_filter_not (fun v : V => c v = c a)
  have ha : 0 < A.card := Finset.card_pos.mpr ⟨a, by simp [A]⟩
  have hN := Fintype.card_pos (α := V)
  have hsum : ∑ v, G.degree v ≤ Fintype.card V * M := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (f := fun v : V => G.degree v) (g := fun _ => M)
      (fun v _ => by rw [hv]; split <;> omega)
  constructor
  · rw [htotal] at hdeg
    have hd : d ≠ 0 := by
      intro he
      rw [he] at hdeg
      simp only [Nat.mul_zero, Nat.le_zero] at hdeg
      exact (Nat.mul_pos hk hN).ne' hdeg
    have hlt := Nat.mul_lt_mul_of_pos_right (show B.card < Fintype.card V by omega)
      (show 0 < 2*d by omega)
    have hsmall : 2*(B.card*d) < (2*d)*Fintype.card V := by
      calc
        _ = B.card*(2*d) := by ac_rfl
        _ < _ := hlt.trans_eq (Nat.mul_comm _ _)
    by_contra! hh
    exact (hdeg.trans_lt hsmall).not_ge (Nat.mul_le_mul_right _ hh)
  · have hh := hdeg.trans hsum
    rw [Nat.mul_comm (Fintype.card V)] at hh
    exact Nat.le_of_mul_le_mul_right hh hN

/-- The final extension needs a degree bound only at the other ends of
two-edge paths from one chosen vertex. -/
theorem radius_add_floor_le_path_of_high_second_neighborhood [Nontrivial V]
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (a : V)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) (hlt : ⌊l G⌋₊ < 2*d)
    (hhigh : ∀ v u, v ≠ a → G.Adj v u → G.Adj u a → ⌊l G⌋₊ ≤ G.degree v) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  let k := ⌊l G⌋₊
  change k < 2*d at hlt
  change ∀ v u, v ≠ a → G.Adj v u → G.Adj u a → k ≤ G.degree v at hhigh
  change G.radius.toNat + k ≤ _
  by_cases hr : G.radius.toNat ≤ 4
  · exact radius_add_floor_le_path_of_bipartite_radius_le_four hc ⟨c⟩ h4 hr
  by_cases hlarge : k < G.radius.toNat
  · have := chung_bound_nat G hc
    omega
  obtain ⟨w, p, hp, hrad⟩ := exists_geodesic_ge_radius G hc a
  have hpr : p.reverse.length = G.dist w a := by rw [Walk.length_reverse, hp, G.dist_comm]
  obtain ⟨P, _, hP⟩ := extend_other_end p.reverse hpr hc c h4 Set.univ (Set.mem_univ _)
    (Set.mem_univ _) (by omega : 3 ≤ d) (hasNeighbors_univ hmin)
    (by rw [Walk.length_reverse]; omega) 2 (by omega) (by rw [Walk.length_reverse]; omega)
  have plen := P.length_le
  rw [Walk.length_reverse] at plen
  by_cases hdone : G.radius.toNat + k ≤ p.length + (2*d-5) + 2 + 1
  · omega
  have hend : P.vertex 2 = a := by
    simpa only [Nat.add_zero, Nat.sub_zero, Walk.getVert_length] using hP 0 (Nat.zero_le _)
  have hn : 2 ≤ p.reverse.length + (2*d-5) + 2 := by omega
  have hdeg := hhigh (P.vertex 0) (P.vertex 1)
    (fun he => by have ht := P.inj (Nat.zero_le _) hn (he.trans hend.symm); omega)
    ((P.edges (Nat.zero_le _) (by omega)).2 (Or.inl rfl))
    (by have he := (P.edges (i := 1) (j := 2) (by omega) hn).2 (Or.inl rfl); rwa [hend] at he)
  have hrev := p.length_reverse
  obtain ⟨Q, _⟩ := P.extend c h4 (by omega) (by omega)
  have hq := Q.length_le
  rw [Walk.length_reverse] at hq
  omega

/-- One part with minimum degree at least the floored average suffices for
the final extension, even when both classes have varying degrees. -/
theorem radius_add_floor_le_path_of_one_high_part [Nontrivial V]
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (a : V)
    {d : ℕ} (hmin : ∀ v, d ≤ G.degree v) (hlt : ⌊l G⌋₊ < 2*d)
    (hhigh : ∀ v, c v = c a → ⌊l G⌋₊ ≤ G.degree v) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  apply radius_add_floor_le_path_of_high_second_neighborhood hc c h4 a hmin hlt
  intro v u _ hv hu
  apply hhigh v
  apply Fin.ext
  have := Fin.val_ne_of_ne (c.valid hv)
  have := Fin.val_ne_of_ne (c.valid hu)
  have := (c v).isLt
  have := (c u).isLt
  have := (c a).isLt
  omega

/-- WOWII 133 for every connected biregular bipartite graph without a four-cycle.
The part containing `a` has the larger of the two valences. -/
theorem radius_add_floor_le_path_of_biregular [Nontrivial V]
    (hc : G.Connected) (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G) (a : V)
    {d M : ℕ} (horder : d ≤ M) (hv : ∀ v, G.degree v = if c v = c a then M else d) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  let k := ⌊l G⌋₊
  change G.radius.toNat + k ≤ _
  by_cases hr : G.radius.toNat ≤ 4
  · exact radius_add_floor_le_path_of_bipartite_radius_le_four hc ⟨c⟩ h4 hr
  by_cases hlarge : k < G.radius.toNat
  · have := chung_bound_nat G hc
    omega
  have hav : (k : ℝ) ≤ l G := Nat.floor_le (by
    unfold l averageIndepNeighbors
    apply div_nonneg
    · apply Finset.sum_nonneg; intro v _; exact Nat.cast_nonneg _
    · positivity)
  obtain ⟨hlt, hM⟩ := biregular_degree_bounds c a horder hv (by omega : 0 < k)
    (sum_degree_ge_of_le_l hav)
  apply radius_add_floor_le_path_of_one_high_part hc c h4 a (d := d)
  · intro v
    rw [hv]
    split <;> omega
  · exact hlt
  · intro v h
    rw [hv, ite_eq_left h]
    exact hM

/-- Side-independent formulation of biregularity: each color class has
constant degree. The two constants can differ arbitrarily. -/
theorem radius_add_floor_le_path_of_constant_degree_on_parts (hc : G.Connected)
    (c : G.Coloring (Fin 2)) (h4 : NoFourCycle G)
    (hreg : ∀ u v, c u = c v → G.degree u = G.degree v) :
    G.radius.toNat + ⌊l G⌋₊ ≤ path G := by
  classical
  let : Nonempty V := hc.nonempty
  obtain ⟨a, _, hmax⟩ := Finset.exists_max_image Finset.univ (fun v : V => G.degree v)
    Finset.univ_nonempty
  by_cases hother : ∃ b, c b ≠ c a
  · obtain ⟨b, hb⟩ := hother
    let : Nontrivial V := ⟨⟨b, a, fun hh => hb (congrArg c hh)⟩⟩
    apply radius_add_floor_le_path_of_biregular hc c h4 a (hmax b (Finset.mem_univ b))
    intro v
    split_ifs with h
    · exact hreg v a h
    · apply hreg v b
      apply Fin.ext
      have := (c b).isLt
      have := (c v).isLt
      have := (c a).isLt
      have := Fin.val_ne_of_ne h
      have := Fin.val_ne_of_ne hb
      omega
  · push Not at hother
    have hpath := radius_add_minDegree_le_path_of_bipartite hc ⟨c⟩ h4
      (d := G.degree a) (fun v => (hreg v a (hother v)).ge)
    have hav := averageIndepNeighbors_le_of_degree_le (G := G) (d := G.degree a)
      (fun v => hmax v (Finset.mem_univ v))
    exact (Nat.add_le_add_left (Nat.floor_le_of_le hav) _).trans hpath

end Wall133
