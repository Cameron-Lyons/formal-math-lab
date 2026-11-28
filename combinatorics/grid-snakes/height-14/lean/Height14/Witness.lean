import Height14.Path
import Height14.Formula

namespace Height14
namespace Witness

/-- A growing path, stored from its current tip back to its starting point. -/
structure Trail where
  tip : Cell
  past : List Cell

def Trail.cells (s : Trail) := s.tip :: s.past

def push (s : Trail) (p : Cell) : Trail := ⟨p, s.cells⟩

def follow (s : Trail) : List Cell → Trail
  | [] => s
  | p :: ps => follow (push s p) ps

theorem follow_cells (s : Trail) (ps : List Cell) :
    (follow s ps).cells = ps.reverse ++ s.cells := by
  induction ps generalizing s with
  | nil => rfl
  | cons p ps ih =>
    rw [follow, ih]
    simp [push, Trail.cells, List.append_assoc]

def shift (o : Nat) (p : Cell) : Cell := (o + p.1, p.2)

/-- The model lists all past squares that could obstruct the continuation.
Every omitted square lies strictly to the left of column o. -/
def Covers (o : Nat) (model actual : Trail) : Prop :=
  actual.tip = shift o model.tip ∧
  ∀ p ∈ actual.past, p.1 < o ∨ p ∈ model.past.map (shift o)

private theorem covers_trans {o d : Nat} {a b c : Trail}
    (h : Covers o b a) (g : Covers d c b) : Covers (o+d) c a := by
  obtain ⟨ht, hp⟩ := h
  obtain ⟨gt, gp⟩ := g
  refine ⟨by simp [ht, gt, shift, Nat.add_assoc], ?_⟩
  intro p hmem
  rcases hp p hmem with hleft | hnear
  · exact Or.inl (by omega)
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hnear
  rcases gp v hv with hleft | hnear
  · exact Or.inl (by simp [shift]; omega)
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hnear
  exact Or.inr (List.mem_map.mpr ⟨u, hu, by simp [shift, Nat.add_assoc]⟩)

def Clear (s : Trail) : List Cell → Prop
  | [] => True
  | p :: ps => 0 < p.1 ∧ Adjacent p s.tip ∧
    (∀ v ∈ s.past, Apart p v) ∧ Clear (push s p) ps

/-- A checked continuation on the small model is valid on the actual path. -/
private theorem grow {o : Nat} (ps : List Cell) {m a : Trail}
    (hc : Covers o m a) (ha : Induced a.cells) (ok : Clear m ps) :
    Covers o (follow m ps) (follow a (ps.map (shift o))) ∧
      Induced (follow a (ps.map (shift o))).cells := by
  induction ps generalizing m a with
  | nil => exact ⟨hc, ha⟩
  | cons p ps ih =>
    obtain ⟨hpos, hadj, hfar, rest⟩ := ok
    obtain ⟨ht, hp⟩ := hc
    apply ih (m := push m p) (a := push a (shift o p)) _ _ rest
    · refine ⟨rfl, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · right; simp [push, Trail.cells, ht]
      rcases hp v hv with hl | hr
      · exact Or.inl hl
      · exact Or.inr (List.mem_cons_of_mem _ hr)
    · change Adjacent (shift o p) a.tip ∧ (∀ z ∈ a.past, Apart (shift o p) z) ∧ _
      refine ⟨?_, ?_, ha⟩
      · simpa [ht, shift, Adjacent, Nat.add_assoc] using hadj
      · intro z hz
        rcases hp z hz with hl | hr
        · have hx : (shift o p).1 = o + p.1 := rfl
          unfold Apart Adjacent
          constructor
          · intro h
            have he := congrArg Prod.fst h
            omega
          · omega
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
          obtain ⟨hne, hna⟩ := hfar u hu
          simp [Apart, shift, Adjacent, Prod.ext_iff, Nat.add_assoc] at hne hna ⊢
          exact ⟨hne, hna⟩

@[instance_reducible] private def instValidFrom (p : Cell) : (ps : List Cell) → Decidable (ValidFrom p ps)
  | [] => isTrue True.intro
  | q :: qs => by
    letI := instValidFrom q qs
    unfold ValidFrom
    infer_instance
attribute [local instance] instValidFrom

private instance (s : Trail) : Decidable (Induced s.cells) :=
  instValidFrom s.tip s.past

private instance (o : Nat) (m a : Trail) : Decidable (Covers o m a) := by
  unfold Covers; infer_instance

@[instance_reducible] private def instClear (s : Trail) : (ps : List Cell) → Decidable (Clear s ps)
  | [] => isTrue True.intro
  | p :: ps => by
    letI := instClear (push s p) ps
    unfold Clear
    infer_instance
attribute [local instance] instClear

private def move (p : Cell) : Char → Cell
  | 'R' => (p.1 + 1, p.2)
  | 'L' => (p.1 - 1, p.2)
  | 'D' => (p.1, p.2 + 1)
  | _ => (p.1, p.2 - 1)

private def walk (start : Cell) (directions : String) : Trail :=
  directions.toList.foldl (fun s d => push s (move s.tip d)) ⟨start, []⟩

/- The starting paths, repeated 52-square path and final paths are given
by unit moves. Each finite geometric check below uses their actual grid coordinates. -/
private def startShort := walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRD"
private def startLong := walk (11,13) "LLLUUULULULULULLDDRDDRRDRDDLLULLDLLUURUULUUUUUUUUURRDDDDRRRDRDRDRDRDRDDRRDRDRRUULULULULULULULULULULLUURRRDRDRDRDRDRDRDRDRDRDRDDDRRRRUULLUULULULULULULULULUURRDRDRDRD"
private def block := (walk (1,4) "DRDRDRDRDRDRDDDRRRRUULLUULULULULULULULULUURRDRDRDRD").cells.reverse
private def model : Trail := ⟨(0,4), [
  (0,3), (0,6), (0,7), (0,9), (0,10), (1,7), (1,8), (1,10), (1,11), (1,12), (1,13), (2,8),
  (2,9), (2,13), (3,9), (3,10), (3,11), (3,13), (4,11), (4,13), (5,11), (5,12), (5,13)]⟩
private def ending (r : Fin 6) : List Cell :=
  match r.val with
  | 0 | 3 => (walk (1,4) "DRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDDDDDRRUUUUUULULULULULULUURRDRRURRDDLDDRD").cells.reverse
  | 1 => (walk (1,4) "DRDRDRDRDRDRDDDRRURRDRRUULULLLULULULULULULULULUURRDRDRDRDRDRDRDRDRRRDRDRDDDRRUUUULULULULLLULULULULUURRDRRURRDDLDDRRURUUURRDDDDLDDRD").cells.reverse
  | 2 => (walk (1,4) "DRDRDRDRDRDRDDDRRRRRURUURURRDDLDDRRURUUUULUURUULLDLDLDLDLDLDDLLUULULULULULULULULUURRDRDRDRDRDRDRDRRURURURURURRRUULLLLDLDLDLDLLULULUURRDRRUR").cells.reverse
  | 4 => (walk (1,4) "DRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDRDDLDDRRURUUUULULULULULULULUURRDRDRRUURRDDDLDDRD").cells.reverse
  | _ => (walk (1,4) "DRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRRURURURUULLDLDLLULULUURRDRRURRRRDRRURRRRDDLLLDLLDDLDLDLDLDLDDDDRRUUURURURURURURURRDDLDLDLDLDLDLDDRRURRDRRUULUURU").cells.reverse
private def small (n : Fin 29) : Trail :=
  match n.val with
  | 0 => walk (0,0) "DDDDDDDDDDDDD"
  | 1 => walk (0,13) "RUULUURUULUURUULUUUR"
  | 2 => walk (0,12) "DRRUULULUUUUUUUUUURRDDDDDDDDD"
  | 3 => walk (0,11) "DDRRRUULULULUUUUUUUUURRRDDLDDRDDLDDRD"
  | 4 => walk (0,12) "DRRRRUULLLULUURRDRRUULULLLUUUUUURRRRDDLLDDRRD"
  | 5 => walk (1,13) "LUURRDRDRRUULUURUUUUUULULLDDRDDDDLDLLUURUULUUUUURRRRRD"
  | 6 => walk (0,12) "DRRUULULUUUURUULUUUURRDDDRDRDDLDLDDRDRDDDRRUUUULUURUUUULULUURRD"
  | 7 => walk (0,11) "DDRRRUULULULUUUUUUUUURRRDDLDDDDDDRDRDRDDDRRUUUULULULUUUURUUURRDDDDLDDRD"
  | 8 => walk (0,8) "DRDDLDDRRURRDRRRRUULLLULLUULULULUURRDRDRDRDRDRRUULULULULULULLLUURRRRDRRURRDDLDDRD"
  | 9 => walk (6,13) "RURURUULLDLDLDLDLLLLUURRRURURURURRRUULLLULULULLDDRDRDDLDLDLLUURUULUUUUURRRRRDRDRDRRUULUL"
  | 10 => walk (2,0) "LLDDDDDDDDDRDDLDDRRURRDRRUULULLUULUUUUUURURURRDDLDLDDDDRDRDRDRDDDRRUUUULULULULUURURUUURRDDDDLDDRD"
  | 11 => walk (5,13) "LULLDLLUURUULUURRDRDDRRDRDRDRRRRUULLLULULULULULULLLUUUUURRDDDRRDRDRDRDRDRDRRUULULULULULULUURRDRRURRDDLDDRD"
  | 12 => walk (5,13) "LULLDLLUURUULUUUUUUUUURRDDDDRRRDRDRDRDRDRDDLLULULULULULLDDRDDRRDRDRDRRRRURUUUULULULULULULULLUURRRDRDRRUURRDDDLDDRD"
  | 13 => walk (9,13) "LUUULULULULULLDDRDDRRDRDDLLULLDLLUURUULUUUUUUUUURRDDDDRRRDRDRDRDRDRDDDRDRRUULUURUULLLULULULULULLUURRRDRDRDRDRDRRUULULUURRD"
  | 14 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRUUUULULULULULULUUUURRDDDRDRDRDRDRDRDDDDDRRUUUUUULULULULULULUURRDRRURRDDLDDRD"
  | 15 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRUUUULULULULULULUUUURRDDDRDRDRDRDRDRDRDDLDDRRURUUUULULULULULULULUURRDRDRRUURRDDDLDDRD"
  | 16 => walk (0,12) "DRRUULULUURRDRDRDDDRRUUUULULULULLLUUUUUURRDDDDRRDRDRDRDRDRDDLDDRRURRDRRRRUULLLULLUULULULULULULULUURRDRDRDRDRDRDRDRDRDRRUULULULULULULUURRDRRURRDDLDDRD"
  | 17 => walk (11,13) "LLLUUULULULULULLDDRDDRRDRDDLLULLDLLUURUULUUUUUUUUURRDDDDRRRDRDRDRDRDRDDRRDRDRRRRUULLLULULULULULULULULULLUURRRDRDRDRDRDRDRDRDRDRRUULULULULULULUURRDRRURRDDLDDRD"
  | 18 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRURRDRRUULULLLULULULULULULUUUURRDDDRDRDRDRDRDRRRDRDRDDDRRUUUULULULULLLULULULULUURRDRRURRDDLDDRRURUUURRDDDDLDDRD"
  | 19 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRRURUURURRDDLDDRRURUUUULUURUULLDLDLDLDLDLDDLLUULULULULULULUUUURRDDDRDRDRDRDRRURURURURURRRUULLLLDLDLDLDLLULULUURRDRRUR"
  | 20 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDDDDDRRUUUUUULULULULULULUURRDRRURRDDLDDRD"
  | 21 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDRDDLDDRRURUUUULULULULULULULUURRDRDRRUURRDDDLDDRD"
  | 22 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRUUUULULULULULULUUUURRDDDRDRDRDRDRRURURURUULLDLDLLULULUURRDRRURRRRDRRURRRRDDLLLDLLDDLDLDLDLDLDDDDRRUUURURURURURURURRDDLDLDLDLDLDLDDRRURRDRRUULUURU"
  | 23 => walk (11,13) "LLLUUULULULULULLDDRDDRRDRDDLLULLDLLUURUULUUUUUUUUURRDDDDRRRDRDRDRDRDRDDRRDRDRRUULULULULULULULULULULLUURRRDRDRDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDDDDDRRUUUUUULULULULULULUURRDRRURRDDLDDRD"
  | 24 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRURRDRRUULULLLULULULULULULULULUURRDRDRDRDRDRDRDRDRRRDRDRDDDRRUUUULULULULLLULULULULUURRDRRURRDDLDDRRURUUURRDDDDLDDRD"
  | 25 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRRRRURUURURRDDLDDRRURUUUULUURUULLDLDLDLDLDLDDLLUULULULULULULULULUURRDRDRDRDRDRDRDRRURURURURURRRUULLLLDLDLDLDLLULULUURRDRRUR"
  | 26 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRRRUULLUULULULULULULULULUURRDRDRDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDDDDDRRUUUUUULULULULULULUURRDRRURRDDLDDRD"
  | 27 => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRRRUULLUULULULULULULULULUURRDRDRDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRDRDRDDLDDRRURUUUULULULULULULULUURRDRDRRUURRDDDLDDRD"
  | _ => walk (0,8) "DRDDLDDRRURRDRRUULULLUULULULUUUUUURRDDDDDRDRDRDRDRDRDDDRRRRUULLUULULULULULULUUUURRDDDRDRDRDRDRDRDRDRDDDRRUUUULULULULULULULULUURRDRDRDRDRDRDRDRRURURURUULLDLDLLULULUURRDRRURRRRDRRURRRRDDLLLDLLDDLDLDLDLDLDDDDRRUUURURURURURURURRDDLDLDLDLDLDLDDRRURRDRRUULUURU"


private def origin (r : Fin 6) := if r = 0 then 16 else 7
private def initial (r : Fin 6) := if r = 0 then startLong else startShort
private def baseWidth (r : Fin 6) := #[30, 25, 26, 21, 22, 29][r.val]!

private def Inside (width : Nat) (cells : List Cell) :=
  ∀ p ∈ cells, p.1 < width ∧ p.2 < 14

private instance (width : Nat) (cells : List Cell) : Decidable (Inside width cells) := by
  unfold Inside; infer_instance

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem block_check : Clear model block ∧ Covers 6 model (follow model block) ∧
    Inside 12 block ∧ block.length = 52 := by native_decide

private theorem end_checks : ∀ r : Fin 6,
    Covers (origin r) model (initial r) ∧ Induced (initial r).cells ∧
    Inside (origin r + 6) (initial r).cells ∧ Clear model (ending r) ∧
    Inside (baseWidth r - origin r) (ending r) ∧
    (initial r).cells.length + (ending r).length = formula (baseWidth r) ∧
    18 ≤ baseWidth r ∧ baseWidth r ≤ 30 ∧ origin r + 6 ≤ baseWidth r ∧
    baseWidth r % 6 = r.val := by native_decide

private theorem short_checks : ∀ i : Fin 29,
    Induced (small i).cells ∧ Inside (i.val+1) (small i).cells ∧
    (small i).cells.length = formula (i.val+1) := by native_decide

/-- After k insertions the tip and all nearby earlier squares reproduce
the original model, translated by 6k columns. -/
private theorem insertions (r : Fin 6) (k : Nat) : ∃ a : Trail,
    Covers (origin r + 6*k) model a ∧ Induced a.cells ∧
    Inside (origin r + 6*k + 6) a.cells ∧
    a.cells.length = (initial r).cells.length + 52*k := by
  obtain ⟨h0, hi, hb, _⟩ := end_checks r
  induction k with
  | zero => exact ⟨initial r, by simpa, hi, by simpa, by simp⟩
  | succ k ih =>
    obtain ⟨a, hc, ha, hbound, hlen⟩ := ih
    obtain ⟨safe, restored, bbound, blen⟩ := block_check
    let o := origin r + 6*k
    let a' := follow a (block.map (shift o))
    obtain ⟨near, good⟩ := grow block hc ha safe
    have restoredAt := covers_trans near restored
    refine ⟨a', ?_, good, ?_, ?_⟩
    · simpa [Nat.mul_succ, Nat.add_assoc] using restoredAt
    · intro z hz
      rw [show a'.cells = _ from follow_cells a (block.map (shift o))] at hz
      rcases List.mem_append.mp hz with hz | hz
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hz)
        obtain ⟨hvx, hvy⟩ := bbound _ hv
        exact ⟨by dsimp [shift, o]; omega, hvy⟩
      · obtain ⟨hx, hy⟩ := hbound _ hz
        exact ⟨by omega, hy⟩
    · simp [a', follow_cells, blen, hlen]; omega

private theorem family (r : Fin 6) (k : Nat) :
    ∃ cells, Snake (baseWidth r + 6*k) cells ∧ cells.length = formula (baseWidth r + 6*k) := by
  obtain ⟨_, _, _, valid, eBound, baseLen, base18, _, margin, _⟩ := end_checks r
  obtain ⟨a, hc, ha, aBound, aLen⟩ := insertions r k
  let o := origin r + 6*k
  let full := follow a ((ending r).map (shift o))
  obtain ⟨_, validFull⟩ := grow (ending r) hc ha valid
  refine ⟨full.cells, ⟨(by simp [Witness.Trail.cells]), ?_, validFull⟩, ?_⟩
  · intro z hz
    rw [show full.cells = _ from follow_cells ..] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp h)
      obtain ⟨hx, hy⟩ := eBound v hv
      exact ⟨by dsimp [shift, o]; omega, hy⟩
    · obtain ⟨hx, hy⟩ := aBound z h
      exact ⟨by omega, hy⟩
  · have count (t : Nat) : formula (baseWidth r + 6*t) = formula (baseWidth r) + 52*t := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [Nat.mul_succ, ← Nat.add_assoc, formula_add_six (by omega), ih]
        omega
    simp only [full, follow_cells, List.length_append, List.length_reverse, List.length_map, aLen,
      count]
    omega

end Witness

/-- For every positive width, an ordered induced path in the actual grid
attains the claimed number of squares. -/
theorem lower (n : Nat) (hn : 0 < n) :
    ∃ cells, Snake n cells ∧ cells.length = formula n := by
  by_cases h : n < 30
  · let i : Fin 29 := ⟨n-1, by omega⟩
    have he : i.val + 1 = n := by dsimp [i]; omega
    obtain ⟨hi,hb,hl⟩ := Witness.short_checks i
    rw [he] at hb hl
    exact ⟨(Witness.small i).cells, ⟨(by simp [Witness.Trail.cells]), hb, hi⟩, hl⟩
  · let r : Fin 6 := ⟨n % 6, by omega⟩
    obtain ⟨_, _, _, _, _, _, _, h30, _, hr⟩ := Witness.end_checks r
    have rem : Witness.baseWidth r % 6 = n % 6 := hr
    have he : Witness.baseWidth r + 6*((n - Witness.baseWidth r)/6) = n := by omega
    simpa only [he] using Witness.family r ((n - Witness.baseWidth r)/6)

end Height14
