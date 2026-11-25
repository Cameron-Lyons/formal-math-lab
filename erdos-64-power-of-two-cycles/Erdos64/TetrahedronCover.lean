import Erdos64.ExtensionSoundness

/-! Power-of-two cycles in abelian voltage covers of the tetrahedron.
The fiber group is an arbitrary additive commutative group, expressed using
Lean's standard-library integer-module interface. No finiteness is needed.

Normalize the three edges incident to vertex 0 to have voltage zero. The
remaining voltages on 12, 13 and 23 are a, b and c. Each word below contains
four, eight or sixteen base labels, with a final return to its first label
understood. The lifted word is a cycle if its total voltage vanishes and its
equal-label positions have distinct fiber coordinates. The word
0130130231031032 always closes. If its lift repeats a vertex, one of six
linear expressions vanishes. The other words handle those coincidences.
All word and collision checks reduce in the kernel. -/

namespace Erdos64.TetrahedronCover

open Lean.Grind

variable {A : Type u} [IntModule A]

/-- The derived graph of an antisymmetric voltage assignment on the darts of K₄. -/
def graph (s : Fin 4 → Fin 4 → A) (rev : ∀ i j, s j i = -s i j) :
    Graph (Fin 4 × A) where
  adj x y := x.1 ≠ y.1 ∧ y.2 = x.2 + s x.1 y.1
  symm := by
    intro x y h
    obtain ⟨different, step⟩ := h
    exact ⟨Ne.symm different, by rw [rev y.1 x.1] at step; grind⟩
  loopless x h := h.1 rfl

theorem minDegreeThree (s : Fin 4 → Fin 4 → A) (rev : ∀ i j, s j i = -s i j) :
    MinDegreeThree (graph s rev) := by
  intro ⟨i,x⟩
  have labels : ∀ i : Fin 4, ∃ j k l : Fin 4, i ≠ j ∧ i ≠ k ∧ i ≠ l ∧
      j ≠ k ∧ j ≠ l ∧ k ≠ l := by decide
  obtain ⟨j,k,l,hij,hik,hil,hjk,hjl,hkl⟩ := labels i
  refine ⟨(j,x+s i j), (k,x+s i k), (l,x+s i l), ⟨hij,rfl⟩, ⟨hik,rfl⟩,
    ⟨hil,rfl⟩, ?_, ?_, ?_⟩
  · exact fun eq => hjk (congrArg Prod.fst eq)
  · exact fun eq => hjl (congrArg Prod.fst eq)
  · exact fun eq => hkl (congrArg Prod.fst eq)

/-- Integral coefficients in the three independent voltages of K₄. -/
private abbrev Coeff := Int × Int × Int

private def plus (x y : Coeff) : Coeff := (x.1+y.1, x.2.1+y.2.1, x.2.2+y.2.2)
private def minus (x y : Coeff) : Coeff := (x.1-y.1, x.2.1-y.2.1, x.2.2-y.2.2)
private def opp (x : Coeff) : Coeff := (-(x.1), -(x.2.1), -(x.2.2))

private def voltage : Fin 4 → Fin 4 → Coeff
  | 1, 2 => (1,0,0)
  | 2, 1 => (-1,0,0)
  | 1, 3 => (0,1,0)
  | 3, 1 => (0,-1,0)
  | 2, 3 => (0,0,1)
  | 3, 2 => (0,0,-1)
  | _, _ => (0,0,0)

private def eval (a b c : A) (p : Coeff) : A :=
  p.1 • a + p.2.1 • b + p.2.2 • c

private theorem eval_plus (a b c : A) (p q : Coeff) :
    eval a b c (plus p q) = eval a b c p + eval a b c q := by
  simp only [eval, plus, IntModule.add_zsmul]
  grind

private theorem eval_minus (a b c : A) (p q : Coeff) :
    eval a b c (minus p q) = eval a b c p - eval a b c q := by
  simp only [eval, minus, IntModule.sub_zsmul]
  grind

private theorem eval_opp (a b c : A) (p : Coeff) :
    eval a b c (opp p) = -eval a b c p := by
  simp only [eval, opp, IntModule.neg_zsmul]
  grind

private def origin : Fin 4 × Coeff := (0,0,0,0)

/-- Successive symbolic lifts, obtained by integrating the voltage along a word. -/
private def trace (w : List (Fin 4)) : List (Fin 4 × Coeff) :=
  match w with
  | [] => []
  | start :: steps => steps.scanl (fun p j => (j, plus p.2 (voltage p.1 j))) (start,0,0,0)

/-- A certificate lists a base word, its return displacement, and possible
coincidences of two positions with the same base vertex, up to sign. -/
private structure Route where
  word : List (Fin 4)
  net : Coeff
  bad : List Coeff

private def point (r : Route) (i : Fin r.word.length) : Fin 4 × Coeff :=
  (trace r.word)[i.val]?.getD origin

private def Correct (r : Route) : Prop :=
  (∀ i : Fin r.word.length,
    let p := point r i
    let q := point r (cycleNext i)
    p.1 ≠ q.1 ∧ (plus p.2 (voltage p.1 q.1) = q.2 ∨
      plus p.2 (voltage p.1 q.1) = plus q.2 r.net)) ∧
  (∀ i j : Fin r.word.length, i < j → (point r i).1 = (point r j).1 →
    let difference := minus (point r i).2 (point r j).2
    difference ∈ r.bad ∨ opp difference ∈ r.bad)

private instance (r : Route) : Decidable (Correct r) := by unfold Correct; dsimp only; apply instDecidableAnd

/-- If the symbolic word closes and no listed difference vanishes, its lift
is a simple cycle. The injection transports the lifted cycle into its host graph. -/
private theorem realize {V : Type v} {G : Graph V} {a b c : A}
    (f : Fin 4 × A → V) (inj : ∀ x y, f x = f y → x = y)
    (edge : ∀ (i j : Fin 4) (x : A), i ≠ j →
      G.adj (f (i,x)) (f (j,x + eval a b c (voltage i j))))
    (r : Route) (ok : Correct r) (closed : eval a b c r.net = 0)
    (clear : ∀ d ∈ r.bad, eval a b c d ≠ 0) : HasCycle G r.word.length := by
  let v (i : Fin r.word.length) : Fin 4 × A := ((point r i).1, eval a b c (point r i).2)
  have sep {i j : Fin r.word.length} (h : i < j) (eq : v i = v j) : False := by
    have l := congrArg Prod.fst eq
    have p := congrArg Prod.snd eq
    change (point r i).1 = (point r j).1 at l
    change eval a b c (point r i).2 = eval a b c (point r j).2 at p
    rcases ok.2 i j h l with h | h
    · apply clear _ h
      rw [eval_minus, p]
      grind
    · apply clear _ h
      rw [eval_opp, eval_minus, p]
      grind
  refine ⟨fun i => f (v i), ?_, ?_⟩
  · intro i j h
    have same := inj _ _ h
    rcases Nat.lt_trichotomy i.val j.val with h | h | h
    · exact False.elim (sep h same)
    · exact Fin.ext h
    · exact False.elim (sep h same.symm)
  · intro i
    obtain ⟨ne, disp⟩ := ok.1 i
    have step := edge (point r i).1 (point r (cycleNext i)).1 (eval a b c (point r i).2) ne
    have eq : eval a b c (point r i).2 + eval a b c (voltage (point r i).1 (point r (cycleNext i)).1) =
        eval a b c (point r (cycleNext i)).2 := by
      rw [← eval_plus]
      rcases disp with h | h
      · rw [h]
      · rw [h, eval_plus, closed]; grind
    rw [eq] at step
    exact step

private def w0123 : Route :=
  ⟨[0,1,2,3], (1,0,1),
   []⟩

private def w0132 : Route :=
  ⟨[0,1,3,2], (0,1,-1),
   []⟩

private def w0213 : Route :=
  ⟨[0,2,1,3], (-1,1,0),
   []⟩

private def w01230213 : Route :=
  ⟨[0,1,2,3,0,2,1,3], (0,1,1),
   [(0,0,1), (1,-1,0), (1,0,1)]⟩

private def w01320123 : Route :=
  ⟨[0,1,3,2,0,1,2,3], (1,1,0),
   [(0,1,-1), (1,0,0)]⟩

private def w01320132 : Route :=
  ⟨[0,1,3,2,0,1,3,2], (0,2,-2),
   [(0,1,-1)]⟩

private def w01320312 : Route :=
  ⟨[0,1,3,2,0,3,1,2], (1,0,-1),
   [(0,0,1), (0,1,-1), (1,-1,0)]⟩

private def w02132013 : Route :=
  ⟨[0,2,1,3,2,0,1,3], (-1,2,-1),
   [(0,1,-1), (1,-1,1)]⟩

private def w02301231 : Route :=
  ⟨[0,2,3,0,1,2,3,1], (1,-1,2),
   [(0,0,1), (1,-1,1), (1,0,1)]⟩

private def w0123023021320132 : Route :=
  ⟨[0,1,2,3,0,2,3,0,2,1,3,2,0,1,3,2], (0,2,0),
   [(0,0,1), (0,0,2), (0,1,-1), (0,1,1), (1,-2,0), (1,-2,1),
    (1,-2,2), (1,-1,-1), (1,-1,0), (1,-1,1), (1,0,1), (1,0,2)]⟩

private def w0130130231031032 : Route :=
  ⟨[0,1,3,0,1,3,0,2,3,1,0,3,1,0,3,2], (0,0,0),
   [(0,0,1), (0,1,-1), (0,1,0), (0,1,1), (0,2,-1), (0,2,0)]⟩

private def w0130230231032032 : Route :=
  ⟨[0,1,3,0,2,3,0,2,3,1,0,3,2,0,3,2], (0,0,0),
   [(0,0,1), (0,0,2), (0,1,-2), (0,1,-1), (0,1,0), (0,1,1)]⟩

private def w0132013201320132 : Route :=
  ⟨[0,1,3,2,0,1,3,2,0,1,3,2,0,1,3,2], (0,4,-4),
   [(0,1,-1), (0,2,-2), (0,3,-3)]⟩

private def w0310312013201321 : Route :=
  ⟨[0,3,1,0,3,1,2,0,1,3,2,0,1,3,2,1], (0,0,-2),
   [(0,1,-2), (0,1,-1), (0,1,0), (0,2,-2), (1,-2,0), (1,-2,2),
    (1,-1,-1), (1,-1,0), (1,-1,1), (1,0,-1), (1,0,0), (1,1,-1)]⟩

private def blocked (a b c : A) : List Coeff → Prop
  | [] => False
  | d :: ds => eval a b c d = 0 ∨ blocked a b c ds

private theorem usable {a b c : A} {ds : List Coeff} (h : ¬ blocked a b c ds) :
    ∀ d ∈ ds, eval a b c d ≠ 0 := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | h'
    · exact fun eq => h (Or.inl eq)
    · exact ih (fun hb => h (Or.inr hb)) d h'

private abbrev Dyadic (G : Graph V) := HasCycle G 4 ∨ HasCycle G 8 ∨ HasCycle G 16

-- The arithmetic between successive collisions is linear over the integers.
local macro "linear_eq" : tactic => `(tactic| grind (splits := 0) only)

private theorem witnesses {V : Type v} {G : Graph V} {a b c : A}
    (f : Fin 4 × A → V) (inj : ∀ x y, f x = f y → x = y)
    (edge : ∀ (i j : Fin 4) (x : A), i ≠ j →
      G.adj (f (i,x)) (f (j,x + eval a b c (voltage i j)))) : Dyadic G := by
  classical
  apply Classical.byContradiction
  intro avoid
  have fails (r : Route) (ok : Correct r)
      (len : r.word.length = 4 ∨ r.word.length = 8 ∨ r.word.length = 16)
      (cl : eval a b c r.net = 0) : blocked a b c r.bad := by
    apply Classical.byContradiction
    intro clear
    have hc := realize f inj edge r ok cl (usable clear)
    rcases len with h | h | h
    · exact avoid (Or.inl (h ▸ hc))
    · exact avoid (Or.inr (Or.inl (h ▸ hc)))
    · exact avoid (Or.inr (Or.inr (h ▸ hc)))
  have h1 := fails w0123 (by decide) (by decide)
  simp only [w0123, blocked, eval] at h1
  have h2 := fails w0132 (by decide) (by decide)
  simp only [w0132, blocked, eval] at h2
  have h3 := fails w0213 (by decide) (by decide)
  simp only [w0213, blocked, eval] at h3
  have h4 := fails w01230213 (by decide) (by decide)
  simp only [w01230213, blocked, eval, or_false] at h4
  have h5 := fails w01320123 (by decide) (by decide)
  simp only [w01320123, blocked, eval, or_false] at h5
  have h6 := fails w01320132 (by decide) (by decide)
  simp only [w01320132, blocked, eval, or_false] at h6
  have h7 := fails w01320312 (by decide) (by decide)
  simp only [w01320312, blocked, eval, or_false] at h7
  have h8 := fails w02132013 (by decide) (by decide)
  simp only [w02132013, blocked, eval, or_false] at h8
  have h9 := fails w02301231 (by decide) (by decide)
  simp only [w02301231, blocked, eval, or_false] at h9
  have h10 := fails w0123023021320132 (by decide) (by decide)
  simp only [w0123023021320132, blocked, eval, or_false] at h10
  have h11 := fails w0130130231031032 (by decide) (by decide)
  simp only [w0130130231031032, blocked, eval, or_false] at h11
  have h12 := fails w0130230231032032 (by decide) (by decide)
  simp only [w0130230231032032, blocked, eval, or_false] at h12
  have h13 := fails w0132013201320132 (by decide) (by decide)
  simp only [w0132013201320132, blocked, eval, or_false] at h13
  have h14 := fails w0310312013201321 (by decide) (by decide)
  simp only [w0310312013201321, blocked, eval, or_false] at h14
  simp only [IntModule.zero_zsmul, IntModule.one_zsmul, AddCommMonoid.zero_add,
    AddCommMonoid.add_zero] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  clear fails edge inj avoid
  -- The following three cases handle collisions after c vanishes.
  have case1 (p1 : c = 0) (p2 : (2 : Int) • b - (2 : Int) • c = 0) : False := by
    have collision := h6 (by linear_eq)
    exact h2 (by linear_eq)
  have case2 (p1 : c = 0) (p2 : a - (2 : Int) • b = 0) : False := by
    have collision := h8 (by linear_eq)
    rcases collision with e | e <;> exact h1 (by linear_eq)
  have case3 (p1 : c = 0) (p2 : a + b - c = 0) : False := by
    have collision := h5 (by linear_eq)
    rcases collision with e | e <;> exact h1 (by linear_eq)
  have case4 (p1 : c = 0) : False := by
    have collision := h14 (by linear_eq)
    rcases collision with e | e | e | e | e | e | e | e | e | e | e | e
    · exact h2 (by linear_eq)
    · exact h2 (by linear_eq)
    · exact h2 (by linear_eq)
    · exact case1 (by linear_eq) (by linear_eq)
    · exact case2 (by linear_eq) (by linear_eq)
    · exact case2 (by linear_eq) (by linear_eq)
    · exact h3 (by linear_eq)
    · exact h3 (by linear_eq)
    · exact h3 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact case3 (by linear_eq) (by linear_eq)
  have case5 (p1 : b + c = 0) : False := by
    have collision := h4 (by linear_eq)
    rcases collision with e | e | e
    · exact h2 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact h1 (by linear_eq)
  have case6 (p1 : (2 : Int) • c = 0) (p2 : (2 : Int) • b - c = 0) : False := by
    have four : (4 : Int) • b + (-4 : Int) • c = 0 := by linear_eq
    have collision := h13 four
    rcases collision with e | e | e
    · exact h2 (by linear_eq)
    · exact case1 (by linear_eq) (by linear_eq)
    · exact h2 (by
        calc b + (-1 : Int) • c = ((4 : Int) • b + (-4 : Int) • c) - ((3 : Int) • b + (-3 : Int) • c) := by grind
             _ = 0 := by rw [four,e]; grind)
  have case7 (p1 : (2 : Int) • b - c = 0) : False := by
    have collision := h12 (by linear_eq)
    rcases collision with e | e | e | e | e | e
    · exact case1 (by linear_eq) (by linear_eq)
    · exact case6 (by linear_eq) (by linear_eq)
    · exact case5 (by linear_eq)
    · exact h2 (by linear_eq)
    · exact h2 (by linear_eq)
    · exact case5 (by linear_eq)
  have case8 (p1 : (2 : Int) • c = 0) (p2 : (2 : Int) • b = 0) : False := by
    have collision := h6 (by linear_eq)
    exact h2 (by linear_eq)
  have case9 (p1 : b - (2 : Int) • c = 0) (p2 : (2 : Int) • b = 0) : False := by
    have four : (4 : Int) • b + (-4 : Int) • c = 0 := by linear_eq
    have collision := h13 four
    rcases collision with e | e | e
    · exact h2 (by linear_eq)
    · exact case8 (by linear_eq) (by linear_eq)
    · exact h2 (by
        calc b + (-1 : Int) • c = ((4 : Int) • b + (-4 : Int) • c) - ((3 : Int) • b + (-3 : Int) • c) := by grind
             _ = 0 := by rw [four,e]; grind)
  have case10 (p1 : b = 0) (p2 : a - (2 : Int) • b + (2 : Int) • c = 0) : False := by
    have collision := h9 (by linear_eq)
    rcases collision with e | e | e <;> exact h1 (by linear_eq)
  have case11 (p1 : b = 0) (p2 : a - b - c = 0) : False := by
    have collision := h7 (by linear_eq)
    rcases collision with e | e | e <;> exact h1 (by linear_eq)
  have case12 (p1 : b = 0) : False := by
    have collision := h10 (by linear_eq)
    rcases collision with e | e | e | e | e | e | e | e | e | e | e | e
    · exact h2 (by linear_eq)
    · exact case8 (by linear_eq) (by linear_eq)
    · exact h2 (by linear_eq)
    · exact h2 (by linear_eq)
    · exact h3 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact case10 (by linear_eq) (by linear_eq)
    · exact case11 (by linear_eq) (by linear_eq)
    · exact h3 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact h1 (by linear_eq)
    · exact case10 (by linear_eq) (by linear_eq)
  have case13 (p1 : (2 : Int) • b = 0) : False := by
    have collision := h12 (by linear_eq)
    rcases collision with e | e | e | e | e | e
    · exact case1 (by linear_eq) (by linear_eq)
    · exact case8 (by linear_eq) (by linear_eq)
    · exact case9 (by simpa only [AddCommGroup.sub_eq_add_neg, ← IntModule.neg_zsmul] using e) p1
    · exact h2 (by linear_eq)
    · exact case12 (by linear_eq)
    · exact h2 (by linear_eq)
  -- The zero-voltage word at the root forces one of the excluded relations.
  have collision := h11 (by linear_eq)
  rcases collision with e | e | e | e | e | e
  · exact case4 (by linear_eq)
  · exact h2 (by linear_eq)
  · exact case12 (by linear_eq)
  · exact case5 (by linear_eq)
  · exact case7 (by linear_eq)
  · exact case13 (by linear_eq)

/-- Every abelian voltage assignment on K₄ gives a graph containing a simple
cycle of length 4, 8, or 16. The assignment is arbitrary on all six edges. -/
theorem cycle_of_abelian_voltage (s : Fin 4 → Fin 4 → A) (rev : ∀ i j, s j i = -s i j) :
    HasCycle (graph s rev) 4 ∨ HasCycle (graph s rev) 8 ∨ HasCycle (graph s rev) 16 := by
  let t (i : Fin 4) : A := if i = 0 then 0 else s 0 i
  let a := t 1 + s 1 2 - t 2
  let b := t 1 + s 1 3 - t 3
  let c := t 2 + s 2 3 - t 3
  let f (p : Fin 4 × A) : Fin 4 × A := (p.1, p.2 + t p.1)
  have inj (x y : Fin 4 × A) (h : f x = f y) : x = y := by
    obtain ⟨i,x⟩ := x
    obtain ⟨j,y⟩ := y
    have same : i = j := congrArg Prod.fst h
    subst j
    have hx : x + t i = y + t i := congrArg Prod.snd h
    have : x = y := by grind
    rw [this]
  have gauge : ∀ (i j : Fin 4), i ≠ j →
      eval a b c (voltage i j) + t j = t i + s i j := by
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
    repeat' constructor
    all_goals
      intro ne
      first | exact False.elim (ne rfl) | skip
    all_goals
      simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two] at *
      dsimp [voltage, eval, a, b, c, t]
      grind
  apply witnesses (a := a) (b := b) (c := c) f inj
  intro i j x ne
  refine ⟨ne, ?_⟩
  change x + eval a b c (voltage i j) + t j = x + t i + s i j
  have := gauge i j ne
  grind

/-- The example has seven sheets, with voltages 1, 3, 2 on the chords 12, 13, 23. -/
def sevenVoltage : Fin 4 → Fin 4 → Fin 7
  | 1, 2 => 1
  | 2, 1 => 6
  | 1, 3 => 3
  | 3, 1 => 4
  | 2, 3 => 2
  | 3, 2 => 5
  | _, _ => 0

def sevenCover := graph sevenVoltage (by decide)

private abbrev Vertex := Fin 4 × Fin 7

/-- Enumerate simple continuations of a partial path, closing to its start
after exactly the prescribed number of fresh vertices. -/
private def closes : Nat → Vertex → Vertex → List Vertex → Bool
  | 0, start, x, _ =>
    decide (x.1 ≠ start.1 ∧ start.2 = x.2 + sevenVoltage x.1 start.1)
  | n+1, start, x, seen =>
    (List.finRange 4).any fun j =>
      let y := (j, x.2 + sevenVoltage x.1 j)
      decide (x.1 ≠ j ∧ y ∉ seen) && closes n start y (y :: seen)

private theorem closes_of_path (p : Nat → Vertex) (start : Vertex) (r i : Nat) (seen : List Vertex)
    (fresh : ∀ k, i < k → k ≤ i+r → p k ∉ seen)
    (distinct : ∀ k l, k < l → l ≤ i+r → p k ≠ p l)
    (edges : ∀ k, i ≤ k → k < i+r → sevenCover.adj (p k) (p (k+1)))
    (last : sevenCover.adj (p (i+r)) start) : closes r start (p i) seen = true := by
  induction r generalizing i seen with
  | zero => exact decide_eq_true last
  | succ r ih =>
    obtain ⟨ne, disp⟩ := edges i (by omega) (by omega)
    have next : ((p (i+1)).1, (p i).2 + sevenVoltage (p i).1 (p (i+1)).1) = p (i+1) :=
      Prod.ext rfl disp.symm
    apply List.any_eq_true.mpr
    refine ⟨(p (i+1)).1, List.mem_finRange _, ?_⟩
    dsimp only
    rw [next, Bool.and_eq_true]
    refine ⟨decide_eq_true ⟨ne, fresh _ (by omega) (by omega)⟩, ih (i+1) _ ?_ ?_ ?_ ?_⟩
    · intro k hk hk' mem
      rcases List.mem_cons.mp mem with eq | h
      · exact (distinct _ _ hk (by omega)) eq.symm
      · exact fresh _ (by omega) (by omega) h
    · intro k l h h'
      exact distinct k l h (by omega)
    · intro k h h'
      exact edges k (by omega) (by omega)
    · simpa only [show i+1+r = i+(r+1) by omega] using last

private theorem noCycle_of_search (r : Nat)
    (none : ∀ (i : Fin 4) (x : Fin 7), closes r (i,x) (i,x) [(i,x)] = false) :
    ¬ HasCycle sevenCover (r+1) := by
  intro ⟨f, inj, step⟩
  let idx (k : Nat) : Fin (r+1) := ⟨k % (r+1), Nat.mod_lt _ (by omega)⟩
  let p (k : Nat) := f (idx k)
  have distinct (k l : Nat) (h : k < l) (hl : l ≤ r) : p k ≠ p l := by
    intro he
    have eq := congrArg Fin.val (inj _ _ he)
    simp only [idx, Nat.mod_eq_of_lt (show k < r+1 by omega),
      Nat.mod_eq_of_lt (show l < r+1 by omega)] at eq
    omega
  have edge (k : Nat) (h : k ≤ r) : sevenCover.adj (p k) (p (k+1)) := by
    have eq : cycleNext (idx k) = idx (k+1) := by
      apply Fin.ext
      simp only [cycleNext, idx, Nat.mod_eq_of_lt (show k < r+1 by omega)]
    simpa only [p, eq] using step (idx k)
  have last : sevenCover.adj (p r) (p 0) := by
    have eq : idx (r+1) = idx 0 := by apply Fin.ext; simp [idx]
    simpa only [p, eq] using edge r (by omega)
  have found := closes_of_path p (p 0) r 0 [p 0] (by
    intro k hk hr
    simpa only [List.mem_singleton] using Ne.symm (distinct 0 k hk (by omega)))
    (by simpa using distinct) (by intro k _ hk; exact edge k (by omega)) (by simpa using last)
  rw [none] at found
  contradiction

/-- Sixteen is necessary even for a cyclic cover on 28 vertices. -/
theorem sevenCover_sharp :
    ¬ HasCycle sevenCover 4 ∧ ¬ HasCycle sevenCover 8 ∧ HasCycle sevenCover 16 := by
  have four := noCycle_of_search 3 (by decide)
  have eight := noCycle_of_search 7 (by decide)
  refine ⟨four, eight, ?_⟩
  rcases cycle_of_abelian_voltage sevenVoltage (by decide) with h | h | h
  · exact False.elim (four h)
  · exact False.elim (eight h)
  · exact h

end Erdos64.TetrahedronCover
