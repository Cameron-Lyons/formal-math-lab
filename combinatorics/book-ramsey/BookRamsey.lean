import Std

namespace BookRamsey

/-- A finite undirected graph without loops, with vertices numbered from zero. -/
structure Graph (n : Nat) where
  adj : Fin n → Fin n → Bool
  symm : ∀ u v, adj u v = adj v u
  loopless : ∀ u, adj u u = false

namespace Graph

/-- The bits strictly above the diagonal specify all unordered pairs. -/
def ofUpper (bits : Fin n → Fin n → Bool) : Graph n where
  adj u v := decide (u ≠ v) && bits (min u v) (max u v)
  symm u v := by
    have hmin : min u v = min v u := Fin.ext (Nat.min_comm u.val v.val)
    have hmax : max u v = max v u := Fin.ext (Nat.max_comm u.val v.val)
    simp [hmin, hmax, ne_comm]
  loopless u := by simp

def complement (g : Graph n) : Graph n where
  adj u v := decide (u ≠ v) && !g.adj u v
  symm u v := by simp [g.symm u v, ne_comm]
  loopless u := by simp

/-- The pages are distinct vertices, each adjacent to both ends of the spine.
Looplessness forces the ends of the spine and every page to be distinct. -/
def BookAt (g : Graph n) (u : Fin n) (k : Nat) : Prop :=
  ∃ v, g.adj u v = true ∧ ∃ pages : List (Fin n),
    pages.Nodup ∧ pages.length = k ∧
    ∀ w ∈ pages, g.adj u w = true ∧ g.adj v w = true

def HasBook (g : Graph n) (k : Nat) : Prop := ∃ u, g.BookAt u k

def commonCount (g : Graph n) (u v : Fin n) : Nat :=
  (List.finRange n).countP (fun w => g.adj u w && g.adj v w)

theorem bookAt_iff (g : Graph n) (u : Fin n) (k : Nat) :
    g.BookAt u k ↔ ∃ v, g.adj u v = true ∧ k ≤ g.commonCount u v := by
  constructor
  · rintro ⟨v, huv, pages, hnodup, hlen, hpages⟩
    refine ⟨v, huv, ?_⟩
    rw [commonCount, List.countP_eq_length_filter, ← hlen]
    apply hnodup.length_le_of_subset
    intro w hw
    simp [List.mem_finRange, (hpages w hw).1, (hpages w hw).2]
  · rintro ⟨v, huv, hcount⟩
    let common := (List.finRange n).filter (fun w => g.adj u w && g.adj v w)
    have hlen : k ≤ common.length := by
      simpa [commonCount, List.countP_eq_length_filter, common] using hcount
    have hn : common.Nodup := List.filter_sublist.nodup (List.nodup_finRange n)
    refine ⟨v, huv, common.take k, (List.take_sublist ..).nodup hn,
      List.length_take_of_le hlen, ?_⟩
    intro w hw
    have hmem := (List.take_sublist k common).subset hw
    exact Bool.and_eq_true_iff.mp (List.mem_filter.mp hmem).2

theorem hasBook_iff (g : Graph n) (k : Nat) :
    g.HasBook k ↔ ∃ u v, g.adj u v = true ∧ k ≤ g.commonCount u v :=
  exists_congr fun u => g.bookAt_iff u k

/-- Discarding pages of a book leaves a smaller book on the same spine. -/
theorem HasBook.mono {g : Graph n} (h : g.HasBook k) (hle : j ≤ k) : g.HasBook j := by
  obtain ⟨u, v, edge, pages⟩ := (g.hasBook_iff k).mp h
  exact (g.hasBook_iff j).mpr ⟨u, v, edge, Nat.le_trans hle pages⟩

/-- A book is absent exactly when every possible spine has too few pages. -/
theorem not_hasBook_iff (g : Graph n) (k : Nat) :
    ¬g.HasBook k ↔ ∀ u v, g.adj u v = true → g.commonCount u v < k := by
  simp only [hasBook_iff, not_exists, not_and, Nat.not_le]

/-- Inspect every ordered pair. A nonedge cannot be a spine. -/
def avoids (g : Graph n) (k : Nat) : Bool :=
  (List.finRange n).all fun u => (List.finRange n).all fun v =>
    decide (g.adj u v = true → g.commonCount u v < k)

theorem avoids_iff (g : Graph n) (k : Nat) :
    g.avoids k = true ↔ ¬g.HasBook k := by
  simp only [avoids, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq, not_hasBook_iff]

def check (g : Graph n) (red blue : Nat) : Bool :=
  g.avoids red && g.complement.avoids blue

theorem check_iff (g : Graph n) (red blue : Nat) :
    g.check red blue = true ↔ ¬g.HasBook red ∧ ¬g.complement.HasBook blue := by
  simp [check, avoids_iff]

def degree (g : Graph n) (u : Fin n) : Nat :=
  (List.finRange n).countP (g.adj u)

private theorem nonedge_count_on (g : Graph n) (u v : Fin n) (huv : u ≠ v)
    (h : g.adj u v = false) (xs : List (Fin n)) :
    xs.countP (fun w => g.complement.adj u w && g.complement.adj v w) +
      xs.countP (g.adj u) + xs.countP (g.adj v) + xs.count u + xs.count v =
    xs.length + xs.countP (fun w => g.adj u w && g.adj v w) := by
  induction xs with
  | nil => rfl
  | cons w xs ih =>
    -- The contribution of w is determined by its two adjacencies and whether it is an endpoint.
    have reverse : g.adj v u = false := (g.symm v u).trans h
    simp only [List.countP_cons, List.count_cons, List.length_cons, complement] at *
    grind [g.loopless]

/-- On a nonedge, inclusion-exclusion relates the red and blue common neighbors. -/
theorem nonedge_commonCount (g : Graph n) (u v : Fin n) (huv : u ≠ v)
    (h : g.adj u v = false) :
    g.complement.commonCount u v + g.degree u + g.degree v + 2 =
      n + g.commonCount u v := by
  have hcount (w : Fin n) : (List.finRange n).count w = 1 :=
    (List.nodup_finRange n).count_of_mem (List.mem_finRange w)
  simpa [commonCount, degree, hcount, Nat.add_assoc] using
    nonedge_count_on g u v huv h (List.finRange n)

end Graph
end BookRamsey
