import FiveDice

namespace FiveDice

/-- Add the counts of a list of rankings, retaining multiplicity. -/
def total (rs : List (List Die)) (w : List Die) : Nat :=
  (rs.map (fun r => ways r w)).sum

/-- Insert a die at each of the possible positions in an order. -/
def insertions (a : Die) : List Die → List (List Die)
  | [] => [[a]]
  | b :: r => (a :: b :: r) :: (insertions a r).map (b :: ·)

/-- All ways to extend any one of these orders by a new die. -/
def extend (a : Die) (rs : List (List Die)) : List (List Die) := rs.flatMap (insertions a)

@[simp] theorem total_nil (w : List Die) : total [] w = 0 := rfl

@[simp] theorem total_cons (r : List Die) (rs : List (List Die)) (w : List Die) :
    total (r :: rs) w = ways r w + total rs w := rfl

@[simp] theorem total_append (rs ss : List (List Die)) (w : List Die) :
    total (rs ++ ss) w = total rs w + total ss w := by simp [total]

private theorem total_prepend_step (b x : Die) (rs : List (List Die)) (w : List Die) :
    total (rs.map (b :: ·)) (x :: w) = total (rs.map (b :: ·)) w +
      if b = x then total rs w else 0 := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, total_cons, ih, ways]
    split <;> omega

private theorem total_prepend_empty (b : Die) (rs : List (List Die)) :
    total (rs.map (b :: ·)) [] = 0 := by induction rs <;> simp [*, ways]

private theorem total_insertions_empty (a : Die) (r : List Die) : total (insertions a r) [] = 0 := by
  cases r <;> simp [insertions, ways, total_prepend_empty]

theorem total_insertions (a : Die) (r w : List Die) (h : a ∉ r) :
    total (insertions a r) w = w.count a * ways r w := by
  induction w generalizing r with
  | nil => simp [total_insertions_empty]
  | cons x w ih =>
    cases r with
    | nil =>
      have prev := ih [] (by simp)
      simp [insertions, ways] at prev
      by_cases eq : a = x <;> simp_all [insertions, ways, Ne.symm]
    | cons b r =>
      have ab : a ≠ b := fun eq => h (by simp [eq])
      have ar : a ∉ r := fun mem => h (List.mem_cons_of_mem _ mem)
      have prev := ih (b :: r) h
      simp only [insertions, total_cons] at prev
      rw [insertions, total_cons, total_prepend_step, ways, ways]
      by_cases ax : a = x <;> by_cases bx : b = x <;>
        simp_all [Ne.symm, Nat.add_mul, Nat.mul_add] <;> omega

/-- A roll counted by `rs` can be completed by choosing any face of die `a`. -/
theorem total_extend (a : Die) (rs : List (List Die)) (w : List Die)
    (h : ∀ r ∈ rs, a ∉ r) : total (extend a rs) w = w.count a * total rs w := by
  induction rs with
  | nil => simp [extend]
  | cons r rs ih =>
    have hr : a ∉ r := h r (by simp)
    have hrs : ∀ s ∈ rs, a ∉ s := fun s hs => h s (by simp [hs])
    simp [extend, total_insertions _ _ _ hr, Nat.mul_add, ← ih hrs]

/-- Insert all the missing dice, in every possible position. -/
private def grow : List Die → List (List Die) → List (List Die)
  | [], rs => rs
  | a :: as, rs => extend a (grow as rs)

/-- Every insertion introduces a die absent from the partial orders. -/
private def fresh : List Die → List (List Die) → Bool
  | [], _ => true
  | a :: as, rs => (grow as rs).all (fun r => !r.contains a) && fresh as rs

/-- Choose one face of each listed die from a word of available faces. -/
def productOfCounts (xs : List Die) (w : List Die) : Nat :=
  (xs.map w.count).prod

private theorem grow_total (xs : List Die) (rs : List (List Die)) (w : List Die)
    (h : fresh xs rs = true) : total (grow xs rs) w = productOfCounts xs w * total rs w := by
  induction xs with
  | nil => simp [grow, productOfCounts]
  | cons b bs ih =>
    simp only [fresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at h
    rw [grow, total_extend _ _ _ (by intro r hr; simpa using h.1 r hr), ih h.2]
    simp [productOfCounts, Nat.mul_assoc]

private theorem product_of_equal (xs : List Die) (w : List Die)
    (h : ∀ b : Die, w.count b = 30) : productOfCounts xs w = 30 ^ xs.length := by
  simp [productOfCounts, h, List.map_const', List.prod_replicate_nat]

/-- Enumerate the four opponents starting just after `d`, taking die numbers modulo five. -/
def opponent (d : Die) (i : Fin 4) : Die := d + i.castSucc + 1

/-- The bits of `m` select a subset of the four opponents. -/
def opponents (d : Die) (m : Fin 16) :=
  ((List.finRange 4).filter (fun i => m.val.testBit i.val)).map (opponent d)

private def remaining (d : Die) (m : Fin 16) :=
  ((List.finRange 4).filter (fun i => !m.val.testBit i.val)).map (opponent d)

private def orders (d : Die) (m : Fin 16) := grow (opponents d m) [[]]
private def selected (d : Die) (m : Fin 16) := (orders d m).map (d :: ·)
private def fullOrders (d : Die) (m : Fin 16) := grow (remaining d m) (selected d m)

/-- For `k` specified opponents, the target for a smallest roll is `30^(k+1)/(k+1)`. -/
def expected (k : Nat) := 30 ^ (k + 1) / (k + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem order_data (d : Die) (m : Fin 16) :
    fresh (opponents d m) [[]] = true ∧
    fresh (remaining d m) (selected d m) = true ∧
    (fullOrders d m).all (fun r => decide (r.length = 5 ∧ r.Nodup)) = true ∧
    (fullOrders d m).length * 202500 =
      30 ^ (remaining d m).length * expected (opponents d m).length := by
  revert d m
  decide

/-- The suffix after each face of the distinguished die, listing all higher owners. -/
def suffixes (d : Die) : List Die → List (List Die)
  | [] => []
  | x :: xs => if d = x then xs :: suffixes d xs else suffixes d xs

/-- Count the rolls in which every selected opponent lands above a face of `d`. -/
def moment (d : Die) (m : Fin 16) (ss : List (List Die)) :=
  (ss.map (productOfCounts (opponents d m))).sum

private theorem moments (d : Die) (m : Fin 16) (w : List Die) :
    total (selected d m) w = moment d m (suffixes d w) := by
  induction w with
  | nil => simp [selected, total_prepend_empty, suffixes, moment]
  | cons x w ih =>
    change total ((orders d m).map (d :: ·)) (x :: w) = _
    rw [total_prepend_step, ← selected, ih]
    by_cases h : d = x
    · subst x
      rw [orders, grow_total _ _ _ (order_data d m).1]
      simp [total, suffixes, moment, ways, Nat.add_comm]
    · simp [suffixes, h]

private theorem total_of_fair (w : List Die) (h : Fair 30 w) (rs : List (List Die))
    (hv : ∀ r ∈ rs, r.length = 5 ∧ r.Nodup) : total rs w = rs.length * 202500 := by
  have counts (r : List Die) (hr : r ∈ rs) : ways r w = 202500 := by
    obtain ⟨len, distinct⟩ := hv r hr
    rw [ways_eq_labelChoices_length (i := 1)]
    exact (target30 _).mp (h.2.2 r len distinct)
  rw [total, List.map_congr_left counts, List.map_const', List.sum_replicate_nat]

/-- If a subset contains `k` opponents, exactly `1/(k+1)` of their joint rolls
with `d` place `d` first in increasing label order. -/
theorem fair_moment (d : Die) (m : Fin 16) (w : List Die) (h : Fair 30 w) :
    moment d m (suffixes d w) = expected (opponents d m).length := by
  obtain ⟨_, hf, hv, hn⟩ := order_data d m
  have full := total_of_fair w h (fullOrders d m) (by simpa using (List.all_eq_true.mp hv))
  rw [hn, fullOrders, grow_total _ _ _ hf, product_of_equal _ _ h.2.1, moments] at full
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) full

end FiveDice
