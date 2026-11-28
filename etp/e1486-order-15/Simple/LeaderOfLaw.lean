import MaxKey
import Simple.TestOfLaw
import Simple.Leader

/-! A table that satisfies the law yields one that also passes the ordering conditions.

Among the tables that satisfy the law and have a given pattern of squares, take one whose
string of bits is largest. A swap of neighbors relabels it into another such table, so it
cannot increase the string. The chosen table need not be a relabeling of the given one. -/

namespace E1486.Test
open E1486.Simple

variable {n w : Nat}

/-- A relabeling, given on labels, that keeps the pattern of squares: it is its own
inverse, it sends squares to squares, and it commutes with squaring on the squares. -/
structure Move (n k j : Nat) (s : Nat → Nat) : Prop where
  lt : ∀ a, a < n → s a < n
  self_inverse : ∀ a, s (s a) = a
  square : ∀ a, s a < k ↔ a < k
  partner : ∀ a, a < k → s (E1486.partner j a) = E1486.partner j (s a)

variable {k j : Nat} {s : Nat → Nat}

def Move.label (h : Move n k j s) : Label n where
  old a := ⟨s a.val, h.lt _ a.isLt⟩
  idx a := ⟨s a.val, h.lt _ a.isLt⟩
  idx_old i := Fin.ext (h.self_inverse i.val)
  old_idx i := Fin.ext (h.self_inverse i.val)

/-- The relabeled table has the same pattern of squares. -/
theorem Move.normal (h : Move n k j s) {m : Fin n → Fin n → Fin n} (d : DiagNormal m k j) :
    DiagNormal (h.label.pull m) k j := by
  refine ⟨d.le_size, d.le_squares, d.parity, ?_, ?_⟩
  · intro a
    exact ((h.label.isSq m a).trans (d.sq_iff _)).trans (h.square a.val)
  · intro a ha
    have hs : s a.val < k := (h.square _).mpr ha
    change s (E1486.square m (h.label.old a)).val = _
    rw [d.diagram (h.label.old a) hs]
    change s (E1486.partner j (s a.val)) = _
    rw [h.partner _ hs, h.self_inverse]

/-- Relabeling a table relabels its arrows. -/
theorem arrows_pull (p : Label n) (m : Fin n → Fin n → Fin n) (a b : Fin n) :
    arrows (p.pull m) a b ↔ arrows m (p.old a) (p.old b) := by
  have diagonal : p.pull m b b = a ↔ m (p.old b) (p.old b) = p.old a := by
    constructor
    · intro e; simpa [Label.pull, p.old_idx] using congrArg p.old e
    · intro e; simp [Label.pull, e, p.idx_old]
  simp only [arrows, Pred, p.row, diagonal]

/-- The string of bits that the test compares. -/
noncomputable def word (k : Nat) (m : Fin n → Fin n → Fin n) : List Bool :=
  (cells n k).map fun c => edge n (pack (arrows m)) c.1 c.2

theorem cells_lt (hk : k ≤ n) {c : Nat × Nat} (hc : c ∈ cells n k) : c.1 < n ∧ c.2 < n := by
  simp only [cells, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨x,hx,y,hy,rfl⟩ | ⟨i,hi,⟨q,hq,rfl⟩|⟨q,hq,rfl⟩⟩ <;>
    constructor <;> dsimp <;> omega

theorem word_pull (h : Move n k j s) (hk : k ≤ n) (m : Fin n → Fin n → Fin n) :
    word k (h.label.pull m) =
      (cells n k).map fun c => edge n (pack (arrows m)) (s c.1) (s c.2) := by
  apply List.map_congr_left
  intro c hc
  obtain ⟨h1,h2⟩ := cells_lt hk hc
  apply Bool.eq_iff_iff.mpr
  exact ((edge_pack _ ⟨c.1,h1⟩ ⟨c.2,h2⟩).trans (arrows_pull ..)).trans
    (edge_pack _ (h.label.old ⟨c.1,h1⟩) (h.label.old ⟨c.2,h2⟩)).symm

local instance : Std.Asymm ((· < ·) : Bool → Bool → Prop) := ⟨by decide⟩
local instance : Std.Trichotomous ((· < ·) : Bool → Bool → Prop) := ⟨by decide⟩

theorem geBits_of_le (g : BitVec w) (l : List (Nat × Nat))
    (h : l.map (fun x => g.getLsbD x.2) ≤ l.map (fun x => g.getLsbD x.1)) :
    geBits g l = true := by
  induction l with
  | nil => rfl
  | cons hd tail ih =>
    rcases hd with ⟨a,b⟩
    change g.getLsbD b :: _ ≤ g.getLsbD a :: _ at h
    have cmp := (List.cons_le_cons_iff (α := Bool)).mp h
    simp only [geBits]
    by_cases same : a = b
    · subst b; simp; apply ih; rcases cmp with bad | h; simp at bad; exact h.2
    · simp [same]
      cases ha : g.getLsbD a <;> cases hb : g.getLsbD b <;> simp_all <;> contradiction

/-- A table whose string is largest among the tables of its pattern that satisfy the law
passes the condition for every move. -/
theorem keeps_of_max (h : Move n k j s) {m : Fin n → Fin n → Fin n} (law : Law m)
    (d : DiagNormal m k j)
    (max : ∀ m' : Fin n → Fin n → Fin n, Law m' → DiagNormal m' k j → word k m' ≤ word k m) :
    keeps n k (pack (arrows m)) s = true := by
  apply geBits_of_le
  have le := max _ (h.label.law law) (h.normal d)
  rw [word_pull h d.le_size] at le
  simpa [word, edge, List.map_map, Function.comp_def] using le

/-- Unfold a swap and squaring, and settle each case by arithmetic. -/
macro "move_cases" : tactic => `(tactic|
  (constructor <;> intros <;> simp only [swap, swapPairs, E1486.partner] <;>
   (repeat' split) <;> omega))

theorem move_fixed {a : Nat} (hk : k ≤ n) (ha : a+1 < j) (hj : j ≤ k) :
    Move n k j (swap a (a+1)) := by move_cases

theorem move_pair {i : Nat} (hk : k ≤ n) (hi : j+2*i+1 < k) :
    Move n k j (swap (j+2*i) (j+2*i+1)) := by move_cases

theorem move_pairs {i : Nat} (hk : k ≤ n) (hi : j+2*i+3 < k) :
    Move n k j (swapPairs (j+2*i)) := by move_cases

theorem move_other {a : Nat} (hp : (k-j)%2 = 0) (lo : k ≤ a) (hi : a+1 < n) :
    Move n k j (swap a (a+1)) := by move_cases

/-- If a table satisfies the law, so does one that also passes the ordering conditions. -/
theorem exists_leading {m : Fin n → Fin n → Fin n} (h : Law m) :
    ∃ (m' : Fin n → Fin n → Fin n) (k j : Nat),
      Law m' ∧ DiagNormal m' k j ∧ leads n k j (pack (arrows m')) = true := by
  obtain ⟨m₀,k,j,law₀,d₀⟩ := normalize_diagonal h
  obtain ⟨m',⟨law,d⟩,hm⟩ := Symmetry.exists_max_key
    (fun u : Fin n → Fin n → Fin n => Law u ∧ DiagNormal u k j) (word k) (cells n k).length
    (fun u => by simp [word]) ⟨m₀,law₀,d₀⟩
  have max := fun u (hu : Law u) (du : DiagNormal u k j) => hm u ⟨hu,du⟩
  have hk := d.le_size
  have hj := d.le_squares
  have hp := d.parity
  refine ⟨m',k,j,law,d,?_⟩
  simp only [leads, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro a ha
    exact keeps_of_max (move_fixed hk (by omega) hj) law d max
  · intro i hi
    exact keeps_of_max (move_pair hk (by omega)) law d max
  · intro i hi
    exact keeps_of_max (move_pairs hk (by omega)) law d max
  · intro i hi
    exact keeps_of_max (move_other hp (by omega) (by omega)) law d max

end E1486.Test
