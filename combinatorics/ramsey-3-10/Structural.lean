import Ramsey39

/-!
# Structural.lean
Pure-kernel Lean 4 proofs of structural constraints on `R(3, k, n)` graphs and `R(3, 10, 40)`:
1. `deg_lt_k`: every vertex in a triangle-free graph with no independent `k`-set has `deg v < k`.
2. `dual_nbhd_no_indep`: removing `N[v]` leaves no independent `(k - 1)`-set.
3. `weighted_mantel` & `mantel_twiceEdges_le`: weighted and unweighted Mantel's theorem via
   double-sum Cauchy-Schwarz.
4. `twiceEdges_partition`: `twiceEdges edge = twiceEdgesOn edge (V \ N[v]) + 2 * ∑_{u ∈ N(v)} deg u`.
5. `r310_40_dichotomy`: every simple, triangle-free 40-vertex graph with no independent 10-set
   is either 9-regular (`180` edges, every `G - N[v]` has `99` edges) or has a vertex `v` of
   degree `d ≤ 8` with `|E(G - N[v])| ≤ 180 - 9 * d`.
-/

namespace Ramsey310.Structural

/-- Degree of vertex `v` in `edge` on `Fin n`. -/
def deg {n : Nat} (edge : Fin n → Fin n → Bool) (v : Fin n) : Nat :=
  orderOf (edge v)

/-- Direct recursive sum over a list. -/
def listSum {α : Type} : List α → (α → Nat) → Nat
  | [], _ => 0
  | a :: t, f => f a + listSum t f

/-- Twice the number of edges induced on `S`. -/
def twiceEdgesOn {n : Nat} (edge : Fin n → Fin n → Bool) (S : List (Fin n)) : Nat :=
  listSum S (fun u => (S.filter (edge u)).length)

/-- Twice the total number of edges in `G`. -/
def twiceEdges {n : Nat} (edge : Fin n → Fin n → Bool) : Nat :=
  listSum (List.finRange n) (deg edge)

/-- Weighted degree `d_w(u) = ∑_{v ∈ N(u)} w(v)`. -/
def wDeg {n : Nat} (edge : Fin n → Fin n → Bool) (w : Fin n → Nat) (u : Fin n) : Nat :=
  listSum ((List.finRange n).filter (edge u)) w

/-! ### Compact summation helpers -/

theorem listSum_le {α : Type} {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) : listSum l f ≤ listSum l g := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a t ih =>
      have := h a List.mem_cons_self
      have := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      simp only [listSum]; omega

theorem listSum_add {α : Type} (l : List α) (f g : α → Nat) :
    listSum l (fun x => f x + g x) = listSum l f + listSum l g := by
  induction l with | nil => rfl | cons a t ih => simp only [listSum, ih]; omega

theorem listSum_const {α : Type} (l : List α) (c : Nat) :
    listSum l (fun _ => c) = l.length * c := by
  induction l with
  | nil => simp [listSum]
  | cons a t ih => simp only [listSum, ih, List.length_cons, Nat.add_mul, Nat.one_mul]; omega

theorem listSum_mul_left {α : Type} (l : List α) (c : Nat) (f : α → Nat) :
    listSum l (fun x => c * f x) = c * listSum l f := by
  induction l with | nil => simp [listSum] | cons a t ih => simp only [listSum, ih, Nat.mul_add]

theorem listSum_filter {α : Type} (l : List α) (p : α → Bool) (g : α → Nat) :
    listSum (l.filter p) g = listSum l (fun x => if p x then g x else 0) := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.filter_cons]; cases hpa : p a <;> simp [listSum, hpa, ih]

theorem filter_length_eq_listSum {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length = listSum l (fun x => if p x then 1 else 0) := by
  rw [← listSum_filter, listSum_const, Nat.mul_one]

theorem listSum_swap {α β : Type} (l1 : List α) (l2 : List β) (h : α → β → Nat) :
    listSum l1 (fun u => listSum l2 (fun v => h u v)) =
    listSum l2 (fun v => listSum l1 (fun u => h u v)) := by
  induction l1 with
  | nil => simp [listSum, listSum_const]
  | cons a t1 ih => simp only [listSum, ih, ← listSum_add]

theorem le_listSum_of_mem {α : Type} {l : List α} {f : α → Nat} {x : α} (hx : x ∈ l) :
    f x ≤ listSum l f := by
  induction l with
  | nil => cases hx
  | cons a t ih =>
      simp only [listSum]
      cases hx with
      | head => omega
      | tail _ ht => have := ih ht; omega

/-! ### Degree upper bound and dual-neighborhood reduction -/

/-- In a triangle-free graph with no independent `k`-set, every vertex has degree `< k`. -/
theorem deg_lt_k {n k : Nat} {edge : Fin n → Fin n → Bool}
    (hs : Simple edge) (htf : TriangleFree edge)
    (hnoIS : ∀ s, Independent edge s → orderOf s < k) (v : Fin n) :
    deg edge v < k :=
  hnoIS (edge v) fun x y hvx hvy => hs.2 y x ▸ htf x v y (hs.2 v x ▸ hvx) hvy

/-- Any independent set disjoint from the closed neighborhood `N[v]` has size `< k`. -/
theorem dual_nbhd_no_indep {n k : Nat} {edge : Fin n → Fin n → Bool}
    (hs : Simple edge)
    (hnoIS : ∀ s, Independent edge s → orderOf s < k + 1) (v : Fin n)
    (s : Fin n → Bool) (hind : Independent edge s)
    (hdisj : ∀ u, s u = true → u ≠ v ∧ edge v u = false) :
    orderOf s < k := by
  let s' : Fin n → Bool := fun x => s x || (x == v)
  have hind' : Independent edge s' := by
    intro x y hx hy
    simp only [s', Bool.or_eq_true, beq_iff_eq] at hx hy
    rcases hx with hx | hxv <;> rcases hy with hy | hyv
    · exact hind x y hx hy
    · rw [hyv]; exact hs.2 v x ▸ (hdisj x hx).2
    · rw [hxv]; exact (hdisj y hy).2
    · rw [hxv, hyv]; exact hs.1 v
  have hlt := hnoIS s' hind'
  have hv_false : s v = false := by
    cases h : s v with
    | false => rfl
    | true => exact absurd rfl (hdisj v h).1
  have hlen : orderOf s' = orderOf s + 1 := by
    unfold orderOf
    rw [filter_length_eq_listSum, filter_length_eq_listSum]
    have hsplit : (fun x : Fin n => if s' x then 1 else 0) =
        (fun x : Fin n => (if s x then 1 else 0) + (if x == v then 1 else 0)) := by
      funext x
      by_cases hxv : x = v
      · subst hxv; simp [s', hv_false]
      · simp [s', hxv]
    rw [hsplit, listSum_add, ← filter_length_eq_listSum]
    have hone : ((List.finRange n).filter (fun x => x == v)).length = 1 := by
      have hnd := (List.nodup_finRange n).filter (fun x => x == v)
      have hsub1 : ∀ x ∈ (List.finRange n).filter (fun x => x == v), x ∈ [v] := fun x hx => by
        have hxv := (List.mem_filter.mp hx).2
        simp only [beq_iff_eq] at hxv; simp [hxv]
      have hsub2 : ∀ x ∈ [v], x ∈ (List.finRange n).filter (fun x => x == v) := fun x hx => by
        simp only [List.mem_singleton] at hx; rw [hx]
        exact List.mem_filter.mpr ⟨List.mem_finRange v, by simp⟩
      have hnd_sing : ([v] : List (Fin n)).Nodup := List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
      have h1 := List.Nodup.length_le_of_subset hnd hsub1
      have h2 := List.Nodup.length_le_of_subset hnd_sing hsub2
      simp at h1 h2; omega
    rw [← filter_length_eq_listSum, hone]
  omega

/-! ### Weighted and unweighted Mantel's theorem -/

private theorem two_mul_le_sq_add_sq_of_le {a b : Nat} (h : a ≤ b) :
    2 * (a * b) ≤ a * a + b * b := by
  have hb : b = a + (b - a) := by omega
  have h1 : b * b = a * a + 2 * (a * (b - a)) + (b - a) * (b - a) := by
    calc b * b = (a + (b - a)) * (a + (b - a)) := by rw [← hb]
      _ = a * a + 2 * (a * (b - a)) + (b - a) * (b - a) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm (b - a) a]; omega
  have h2 : 2 * (a * b) = 2 * (a * a) + 2 * (a * (b - a)) := by
    calc 2 * (a * b) = 2 * (a * (a + (b - a))) := by rw [← hb]
      _ = 2 * (a * a) + 2 * (a * (b - a)) := by rw [Nat.mul_add, Nat.mul_add]
  omega

theorem two_mul_le_sq_add_sq (a b : Nat) : 2 * (a * b) ≤ a * a + b * b :=
  (Nat.le_total a b).elim two_mul_le_sq_add_sq_of_le
    (fun h => by rw [Nat.mul_comm a b, Nat.add_comm (a * a)]; exact two_mul_le_sq_add_sq_of_le h)

/-- Weighted Cauchy-Schwarz over `Nat` via double summation. -/
theorem weighted_cauchy_schwarz_nat {α : Type} (l : List α) (w f : α → Nat) :
    listSum l (fun x => w x * f x) * listSum l (fun x => w x * f x) ≤
    listSum l w * listSum l (fun x => w x * (f x * f x)) := by
  let S := listSum l (fun x => w x * f x)
  let W := listSum l w
  let Q := listSum l (fun x => w x * (f x * f x))
  have hle :
      listSum l (fun x => listSum l (fun y => w x * w y * (2 * (f x * f y)))) ≤
      listSum l (fun x => listSum l (fun y => w x * w y * (f x * f x + f y * f y))) :=
    listSum_le fun x _ => listSum_le fun y _ => Nat.mul_le_mul_left _ (two_mul_le_sq_add_sq _ _)
  have hlhs : listSum l (fun x => listSum l (fun y => w x * w y * (2 * (f x * f y)))) = 2 * (S * S) := by
    have h1 : (fun x => listSum l (fun y => w x * w y * (2 * (f x * f y)))) =
        (fun x => (2 * S) * (w x * f x)) := by
      funext x
      rw [show (fun y => w x * w y * (2 * (f x * f y))) = (fun y => (2 * (w x * f x)) * (w y * f y)) from by
            funext y; ac_rfl, listSum_mul_left]
      show 2 * (w x * f x) * S = _; ac_rfl
    rw [h1, listSum_mul_left]; show 2 * S * S = _; ac_rfl
  have hrhs : listSum l (fun x => listSum l (fun y => w x * w y * (f x * f x + f y * f y))) = 2 * (W * Q) := by
    have h1 : (fun x => listSum l (fun y => w x * w y * (f x * f x + f y * f y))) =
        (fun x => W * (w x * (f x * f x)) + Q * w x) := by
      funext x
      rw [show (fun y => w x * w y * (f x * f x + f y * f y)) =
            (fun y => (w x * (f x * f x)) * w y + w x * (w y * (f y * f y))) from by
            funext y; rw [Nat.mul_add]; congr 1 <;> ac_rfl,
          listSum_add, listSum_mul_left, listSum_mul_left]
      show w x * (f x * f x) * W + w x * Q = _; rw [Nat.mul_comm _ W, Nat.mul_comm _ Q]
    rw [h1, listSum_add, listSum_mul_left, listSum_mul_left]
    show W * Q + Q * W = 2 * (W * Q); rw [Nat.mul_comm Q W]; omega
  rw [hlhs, hrhs] at hle; change S * S ≤ W * Q; omega

theorem wDeg_add_wDeg_le {n : Nat} {edge : Fin n → Fin n → Bool} (w : Fin n → Nat)
    (hs : Simple edge) (htf : TriangleFree edge)
    {u v : Fin n} (huv : edge u v = true) :
    wDeg edge w u + wDeg edge w v ≤ listSum (List.finRange n) w := by
  unfold wDeg; rw [listSum_filter, listSum_filter, ← listSum_add]
  refine listSum_le fun x _ => ?_
  cases hux : edge u x with
  | false => cases edge v x <;> simp
  | true =>
      have hvx : edge v x = false := hs.2 x v ▸ htf v u x (hs.2 u v ▸ huv) hux
      simp [hvx]

/-- Weighted Mantel's theorem: for any simple triangle-free graph and vertex weights `w`,
    `2 * ∑_u w(u) * d_w(u) ≤ (∑_u w(u))^2`. -/
theorem weighted_mantel {n : Nat} {edge : Fin n → Fin n → Bool} (w : Fin n → Nat)
    (hs : Simple edge) (htf : TriangleFree edge) :
    2 * listSum (List.finRange n) (fun u => w u * wDeg edge w u) ≤
    listSum (List.finRange n) w * listSum (List.finRange n) w := by
  let V := List.finRange n
  let W := listSum V w
  let S := listSum V (fun u => w u * wDeg edge w u)
  let Q := listSum V (fun u => w u * (wDeg edge w u * wDeg edge w u))
  have h1 :
      listSum V (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * (wDeg edge w u + wDeg edge w v))) ≤
      listSum V (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * W)) :=
    listSum_le fun u _ => Nat.mul_le_mul_left _ (listSum_le fun v hv =>
      Nat.mul_le_mul_left _ (wDeg_add_wDeg_le w hs htf (List.mem_filter.mp hv).2))
  have hrhs : listSum V (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * W)) = W * S := by
    have : (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * W)) = (fun u => W * (w u * wDeg edge w u)) := by
      funext u
      rw [show (fun v => w v * W) = (fun v => W * w v) from by funext v; ac_rfl, listSum_mul_left]
      show w u * (W * wDeg edge w u) = _; ac_rfl
    rw [this, listSum_mul_left]
  have hlhs : listSum V (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * (wDeg edge w u + wDeg edge w v))) = 2 * Q := by
    have hsplit : (fun u => w u * listSum (V.filter (edge u)) (fun v => w v * (wDeg edge w u + wDeg edge w v))) =
        (fun u => w u * (wDeg edge w u * wDeg edge w u) +
          listSum V (fun v => if edge u v then w u * (w v * wDeg edge w v) else 0)) := by
      funext u
      rw [show (fun v => w v * (wDeg edge w u + wDeg edge w v)) =
            (fun v => wDeg edge w u * w v + w v * wDeg edge w v) from by funext v; rw [Nat.mul_add, Nat.mul_comm (w v)],
          listSum_add, listSum_mul_left, Nat.mul_add]
      congr 1; rw [listSum_filter, ← listSum_mul_left]; congr 1; funext v; cases edge u v <;> simp
    rw [hsplit, listSum_add, listSum_swap]
    have hswap : listSum V (fun v => listSum V (fun u => if edge u v then w u * (w v * wDeg edge w v) else 0)) = Q := by
      congr 1; funext v
      rw [show (fun u => if edge u v then w u * (w v * wDeg edge w v) else 0) =
            (fun u => if edge v u then (w v * wDeg edge w v) * w u else 0) from by funext u; rw [hs.2 u v, Nat.mul_comm (w u)],
          ← listSum_filter, listSum_mul_left]
      show w v * wDeg edge w v * wDeg edge w v = _; ac_rfl
    rw [hswap]; show Q + Q = 2 * Q; omega
  rw [hlhs, hrhs] at h1
  have hcs : S * S ≤ W * Q := weighted_cauchy_schwarz_nat V w (wDeg edge w)
  by_cases hS : S = 0
  · change 2 * S ≤ W * W; rw [hS]; exact Nat.zero_le _
  · have hchain : (2 * S) * S ≤ (W * W) * S := by
      calc (2 * S) * S = 2 * (S * S) := Nat.mul_assoc 2 S S
        _ ≤ 2 * (W * Q) := Nat.mul_le_mul_left 2 hcs
        _ = W * (2 * Q) := by ac_rfl
        _ ≤ W * (W * S) := Nat.mul_le_mul_left W h1
        _ = (W * W) * S := (Nat.mul_assoc W W S).symm
    exact Nat.le_of_mul_le_mul_right hchain (Nat.pos_of_ne_zero hS)

theorem exists_pos_weight_le {α : Type} (l : List α) (w f : α → Nat) (bound : Nat)
    (hpos : 0 < listSum l w)
    (hsum : 2 * listSum l (fun x => w x * f x) ≤ listSum l w * bound) :
    ∃ x ∈ l, 0 < w x ∧ 2 * f x ≤ bound := by
  induction l with
  | nil => simp [listSum] at hpos
  | cons a t ih =>
      simp only [listSum] at hsum hpos
      by_cases hwa : 0 < w a
      · by_cases hfa : 2 * f a ≤ bound
        · exact ⟨a, List.mem_cons_self, hwa, hfa⟩
        · have hwa_gt : w a * bound < 2 * (w a * f a) := by
            rw [show 2 * (w a * f a) = w a * (2 * f a) from by ac_rfl]
            exact Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge hfa) hwa
          rw [Nat.mul_add, Nat.add_mul] at hsum
          have htpos : 0 < listSum t w := by
            by_cases ht0 : listSum t w = 0
            · rw [ht0, Nat.zero_mul] at hsum; omega
            · exact Nat.pos_of_ne_zero ht0
          obtain ⟨x, hx, h1, h2⟩ := ih htpos (by omega)
          exact ⟨x, List.mem_cons_of_mem a hx, h1, h2⟩
      · have hwa0 : w a = 0 := by omega
        simp only [hwa0, Nat.zero_mul, Nat.zero_add] at hsum hpos
        obtain ⟨x, hx, h1, h2⟩ := ih hpos hsum
        exact ⟨x, List.mem_cons_of_mem a hx, h1, h2⟩

/-- Standard Mantel's theorem as the `w ≡ 1` specialization of `weighted_mantel`. -/
theorem mantel_twiceEdges_le {n : Nat} {edge : Fin n → Fin n → Bool}
    (hs : Simple edge) (htf : TriangleFree edge) :
    2 * twiceEdges edge ≤ n * n := by
  have h := weighted_mantel (edge := edge) (fun _ => 1) hs htf
  have hw : listSum (List.finRange n) (fun _ => 1) = n := by simp [listSum_const]
  have hd : (fun u => 1 * wDeg edge (fun _ => 1) u) = deg edge := by
    funext u; simp [wDeg, deg, orderOf, listSum_const]
  rw [hd, hw] at h; exact h

theorem mantel_exists_low_deg {n : Nat} {edge : Fin n → Fin n → Bool}
    (hn : 0 < n) (hs : Simple edge) (htf : TriangleFree edge) :
    ∃ v : Fin n, 2 * deg edge v ≤ n := by
  have h := exists_pos_weight_le (List.finRange n) (fun _ => 1) (deg edge) n
    (by simp [listSum_const, hn])
    (by simp [listSum_const]; exact mantel_twiceEdges_le hs htf)
  obtain ⟨v, _, _, hv⟩ := h; exact ⟨v, hv⟩

/-! ### Neighborhood edge-partition identity -/

/-- For any simple triangle-free graph `G` and vertex `v`:
    `twiceEdges G = twiceEdgesOn G (V \ N[v]) + 2 * ∑_{u ∈ N(v)} deg(u)`. -/
theorem twiceEdges_partition {n : Nat} {edge : Fin n → Fin n → Bool}
    (hs : Simple edge) (htf : TriangleFree edge) (v : Fin n) :
    twiceEdges edge =
      twiceEdgesOn edge ((List.finRange n).filter (fun x => x != v && !(edge v x))) +
      2 * listSum ((List.finRange n).filter (edge v)) (deg edge) := by
  let V := List.finRange n
  let isH : Fin n → Bool := fun x => x != v && !(edge v x)
  have hE : twiceEdges edge = listSum V (fun x => listSum V (fun y => if edge x y then 1 else 0)) := by
    unfold twiceEdges deg orderOf; congr 1; funext x; exact filter_length_eq_listSum V (edge x)
  have hH : twiceEdgesOn edge (V.filter isH) =
      listSum V (fun x => listSum V (fun y => if isH x && isH y && edge x y then 1 else 0)) := by
    unfold twiceEdgesOn; rw [listSum_filter]; congr 1; funext x
    cases isH x with
    | false => simp [listSum_const]
    | true => simp [filter_length_eq_listSum]; congr 1; funext y; cases isH y <;> cases edge x y <;> rfl
  have hN1 : listSum (V.filter (edge v)) (deg edge) =
      listSum V (fun x => listSum V (fun y => if edge v x && edge x y then 1 else 0)) := by
    rw [listSum_filter]; congr 1; funext x
    cases edge v x with
    | false => simp [listSum_const]
    | true => exact filter_length_eq_listSum V (edge x)
  have hN2 : listSum (V.filter (edge v)) (deg edge) =
      listSum V (fun x => listSum V (fun y => if edge v y && edge x y then 1 else 0)) := by
    rw [hN1, listSum_swap]; congr 1; funext y; congr 1; funext x; rw [hs.2 y x]
  have hpoint : ∀ x y : Fin n,
      (if edge x y then 1 else 0) =
      (if isH x && isH y && edge x y then 1 else 0) +
      ((if edge v x && edge x y then 1 else 0) + (if edge v y && edge x y then 1 else 0)) := by
    intro x y
    cases hxy : edge x y with
    | false => simp
    | true =>
        cases hvx : edge v x with
        | true =>
            have hvy : edge v y = false := hs.2 y v ▸ htf v x y hvx hxy
            simp [isH, hvx, hvy]
        | false =>
            cases hvy : edge v y with
            | true => simp [isH, hvx, hvy]
            | false =>
                have hxv : (x != v) = true := bne_iff_ne.mpr (fun h => by subst h; rw [hxy] at hvy; contradiction)
                have hyv : (y != v) = true := bne_iff_ne.mpr (fun h => by subst h; rw [hs.2, hxy] at hvx; contradiction)
                simp [isH, hvx, hvy, hxv, hyv]
  rw [hE, hH, Nat.two_mul]
  rw [show (fun x => listSum V (fun y => if edge x y then 1 else 0)) =
        (fun x => listSum V (fun y => if isH x && isH y && edge x y then 1 else 0) +
          (listSum V (fun y => if edge v x && edge x y then 1 else 0) +
           listSum V (fun y => if edge v y && edge x y then 1 else 0))) from by
      funext x; rw [← listSum_add, ← listSum_add]; congr 1; funext y; exact hpoint x y]
  rw [listSum_add, listSum_add, ← hN1, ← hN2]

/-! ### Angeltveit-type `R(3, 10, 40)` dichotomy -/

/-- Every simple, triangle-free 40-vertex graph with no independent 10-set is either
    9-regular (`|E| = 180`, every `G - N[v]` has `99` edges) or has a vertex `v` of degree
    `d ≤ 8` with `|E(G - N[v])| ≤ 180 - 9 * d`. -/
theorem r310_40_dichotomy {edge : Fin 40 → Fin 40 → Bool}
    (hs : Simple edge) (htf : TriangleFree edge)
    (hnoIS : ∀ s, Independent edge s → orderOf s < 10) :
    ((∀ v : Fin 40, deg edge v = 9) ∧ twiceEdges edge = 360 ∧
      ∀ v : Fin 40, twiceEdgesOn edge ((List.finRange 40).filter (fun x => x != v && !(edge v x))) = 198) ∨
    (∃ v : Fin 40, deg edge v ≤ 8 ∧
      twiceEdgesOn edge ((List.finRange 40).filter (fun x => x != v && !(edge v x))) + 18 * deg edge v ≤ 360) := by
  have hdeg9 : ∀ u : Fin 40, deg edge u ≤ 9 := fun u => Nat.le_of_lt_succ (deg_lt_k hs htf hnoIS u)
  let V := List.finRange 40
  let w : Fin 40 → Nat := fun u => 9 - deg edge u
  let W := listSum V w
  have hE_W : twiceEdges edge + W = 360 := by
    change listSum V (deg edge) + listSum V w = 360
    rw [← listSum_add, show (fun x => deg edge x + w x) = (fun _ => 9) from by
      funext x; have := hdeg9 x; simp only [w]; omega, listSum_const]; decide
  by_cases hW0 : W = 0
  · left
    have hall9 : ∀ v : Fin 40, deg edge v = 9 := fun v => by
      have hwv : w v ≤ W := le_listSum_of_mem (List.mem_finRange v)
      have := hdeg9 v; simp only [w] at hwv; omega
    refine ⟨hall9, by omega, fun v => ?_⟩
    have hpart := twiceEdges_partition hs htf v
    have hN : listSum ((List.finRange 40).filter (edge v)) (deg edge) = 81 := by
      rw [show deg edge = (fun _ => 9) from funext hall9, listSum_const]
      exact congrArg (· * 9) (hall9 v)
    rw [hN] at hpart; omega
  · right
    obtain ⟨v, _, hwv, h2dw⟩ :=
      exists_pos_weight_le V w (wDeg edge w) W (Nat.pos_of_ne_zero hW0) (weighted_mantel w hs htf)
    have hdv8 : deg edge v ≤ 8 := by simp only [w] at hwv; omega
    have hpart := twiceEdges_partition hs htf v
    have hN_w : listSum ((List.finRange 40).filter (edge v)) (deg edge) + wDeg edge w v = 9 * deg edge v := by
      unfold wDeg; rw [← listSum_add, show (fun u => deg edge u + w u) = (fun _ => 9) from by
        funext u; have := hdeg9 u; simp only [w]; omega, listSum_const, Nat.mul_comm]; rfl
    exact ⟨v, hdv8, by omega⟩

end Ramsey310.Structural
