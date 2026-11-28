import Std

/-! A word lists the owners of the faces in order of increasing label. The first
entry owns label 1. A ranking lists the dice in order of increasing roll. -/
namespace FiveDice

abbrev Die := Fin 5

/-- All candidate rankings of a specified length, initially allowing repeats. -/
def tuples : Nat → List (List Die)
  | 0 => [[]]
  | n + 1 => (List.finRange 5).flatMap fun a => (tuples n).map (a :: ·)

theorem mem_tuples (r : List Die) (n : Nat) : r ∈ tuples n ↔ r.length = n := by
  induction n generalizing r with
  | zero => simp [tuples]
  | succ n ih =>
    cases r with
    | nil => simp [tuples]
    | cons a r => simp [tuples, ih]

def rankings : List (List Die) := (tuples 5).filter fun r => decide r.Nodup

theorem mem_rankings (r : List Die) : r ∈ rankings ↔ r.length = 5 ∧ r.Nodup := by
  simp [rankings, mem_tuples]

/-- Enumerate the strictly increasing label choices that give `r`. At a face,
each choice either skips the label or uses it for the first die in `r`. -/
def labelChoices : (r w : List Die) → (firstLabel : Nat) → List (List Nat)
  | [], _, _ => [[]]
  | _ :: _, [], _ => []
  | a :: r, x :: w, i =>
    labelChoices (a :: r) w (i + 1) ++
      if a = x then (labelChoices r w (i + 1)).map (i :: ·) else []
termination_by _ w _ => w.length

/-- The enumerator picks exactly the labels whose owners, read in increasing
label order, form the specified ranking. `zipIdx` attaches the actual labels
to the dice, so different faces with the same owner remain distinguishable. -/
theorem mem_labelChoices (r w : List Die) (i : Nat) (labels : List Nat) :
    labels ∈ labelChoices r w i ↔
      labels.length = r.length ∧ (r.zip labels).Sublist (w.zipIdx i) := by
  induction w generalizing r i labels with
  | nil => cases r <;> cases labels <;> simp [labelChoices]
  | cons x w ih =>
    cases r with
    | nil => simp [labelChoices]
    | cons a r =>
      cases labels with
      | nil => by_cases h : a = x <;> simp [labelChoices, h, ih]
      | cons j ls =>
        by_cases h : a = x <;>
          simp [labelChoices, h, ih, List.sublist_cons_iff] <;> grind

/-- No concrete roll is counted twice. -/
theorem labelChoices_nodup (r w : List Die) (i : Nat) : (labelChoices r w i).Nodup := by
  induction w generalizing r i with
  | nil => cases r <;> simp [labelChoices]
  | cons x w ih =>
    cases r with
    | nil => simp [labelChoices]
    | cons a r =>
      by_cases h : a = x
      · simp only [labelChoices, h, ↓reduceIte, List.nodup_append]
        refine ⟨ih _ _, ?_, ?_⟩
        · simpa [List.Nodup, List.pairwise_map] using ih r (i + 1)
        · intro l hl m hm eq
          obtain ⟨t, _, rfl⟩ := List.mem_map.mp hm
          subst l
          have sub := ((mem_labelChoices _ _ _ _).mp hl).2
          have mem : (a, i) ∈ w.zipIdx (i + 1) := sub.subset (by simp [h])
          have bound := List.le_snd_of_mem_zipIdx mem
          exact Nat.not_succ_le_self i bound
      · simpa [labelChoices, h] using ih (a :: r) (i + 1)

/-- Count ways to obtain the ranking `r` from the labeled faces `w`. -/
def ways : (r w : List Die) → Nat
  | [], _ => 1
  | _ :: _, [] => 0
  | a :: r, x :: w => ways (a :: r) w + if a = x then ways r w else 0
termination_by _ w => w.length

theorem ways_eq_labelChoices_length (r w : List Die) (i : Nat) :
    ways r w = (labelChoices r w i).length := by
  induction w generalizing r i with
  | nil => cases r <;> simp [ways, labelChoices]
  | cons x w ih =>
    cases r with
    | nil => simp [ways, labelChoices]
    | cons a r => by_cases h : a = x <;> simp [ways, labelChoices, h, ← ih]

private def suffixCounts (w : List Die) : List Die → List Nat
  | [] => [1]
  | a :: r => ways (a :: r) w :: suffixCounts w r

private theorem suffixCounts_head (w r : List Die) :
    (suffixCounts w r).head?.getD 0 = ways r w := by cases r <;> simp [suffixCounts, ways]

/-- Update all suffixes of one ranking together when adding one smaller face. -/
private def step (x : Die) : List Die → List Nat → List Nat
  | [], _ => [1]
  | a :: r, ns =>
    let tail := ns.drop 1
    (ns.headD 0 + if a = x then tail.headD 0 else 0) :: step x r tail

private theorem step_correct (x : Die) (r w : List Die) :
    step x r (suffixCounts w r) = suffixCounts (x :: w) r := by
  induction r with
  | nil => rfl
  | cons a r ih => simp [step, suffixCounts, ways, suffixCounts_head, ih]

private theorem fold_correct (r w : List Die) :
    w.foldr (fun x ns => step x r ns) (suffixCounts [] r) = suffixCounts w r := by
  induction w with
  | nil => rfl
  | cons x w ih => simp [ih, step_correct]

/-- Dynamic program for one ranking. It keeps one count per suffix. -/
def countRanking (r w : List Die) : Nat :=
  (w.foldr (fun x ns => step x r ns) (suffixCounts [] r)).headD 0

theorem countRanking_correct (r w : List Die) : countRanking r w = ways r w := by
  simp [countRanking, fold_correct, suffixCounts_head]

def Fair (faces : Nat) (w : List Die) : Prop :=
  w.length = 5 * faces ∧ (∀ d : Die, w.count d = faces) ∧
    ∀ r : List Die, r.length = 5 → r.Nodup →
      120 * (labelChoices r w 1).length = faces ^ 5

/-- Certify the word, checking exact integer counts so rounding is impossible. -/
def check (faces : Nat) (w : List Die) : Bool :=
  w.length == 5 * faces && (List.finRange 5).all (fun d => w.count d == faces) &&
    rankings.all (fun r => 120 * countRanking r w == faces ^ 5)

theorem check_iff_fair (faces : Nat) (w : List Die) : check faces w = true ↔ Fair faces w := by
  simp [check, Fair, List.all_eq_true, mem_rankings, countRanking_correct,
    ways_eq_labelChoices_length (i := 1), and_assoc]

/-- Each ordering needs precisely this many of the 24,300,000 rolls. -/
theorem target30 (n : Nat) : 120 * n = 30 ^ 5 ↔ n = 202500 := by omega

theorem check30_iff (w : List Die) :
    check 30 w = true ↔ w.length = 150 ∧ (∀ d : Die, w.count d = 30) ∧
      ∀ r : List Die, r.length = 5 → r.Nodup → (labelChoices r w 1).length = 202500 := by
  simp only [check_iff_fair, Fair, target30, Nat.reduceMul]

theorem necessary_divisibility {faces : Nat} {w : List Die} (h : Fair faces w) :
    120 ∣ faces ^ 5 := by
  exact ⟨_, (h.2.2 [0, 1, 2, 3, 4] rfl (by decide)).symm⟩

theorem only_smaller_face_count {faces : Nat} {w : List Die}
    (positive : 0 < faces) (smaller : faces < 60) (h : Fair faces w) : faces = 30 := by
  have arithmetic : ∀ n : Fin 60, 0 < n.val → 120 ∣ n.val ^ 5 → n.val = 30 := by decide
  exact arithmetic ⟨faces, smaller⟩ positive (necessary_divisibility h)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 800000 in
theorem rankings_length : rankings.length = 120 := by decide

end FiveDice
