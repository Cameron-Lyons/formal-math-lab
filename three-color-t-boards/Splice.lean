import EfficientCheck
import SortedFamily

namespace TBoards.Splice

/-- Row shape and palette for a piece starting at row `k`. -/
def rowsOK (k : Nat) : Board → Bool
  | [] => true
  | row :: rest =>
    decide (row.length = 2*k+1) && row.all (· < 3) && rowsOK (k+1) rest

private theorem rowsOK_append (k : Nat) (a b : Board) :
    rowsOK k (a ++ b) = (rowsOK k a && rowsOK (k+a.length) b) := by
  induction a generalizing k with
  | nil => simp [rowsOK]
  | cons row rest ih =>
    simp [rowsOK, ih, Bool.and_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem rowsOK_get {k : Nat} {b : Board} (h : rowsOK k b = true)
    {i : Nat} (hi : i < b.length) : (b.getD i []).length = 2*(k+i)+1 := by
  induction b generalizing k i with
  | nil => simp at hi
  | cons row rest ih =>
    simp only [rowsOK, Bool.and_eq_true_iff, decide_eq_true_eq] at h
    cases i with
    | zero => simpa using h.1.1
    | succ i =>
      have ht := ih (k := k+1) h.2 (i := i) (by simpa using hi)
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht

private theorem rowsOK_colors {k : Nat} {b : Board} (h : rowsOK k b = true) :
    ∀ row ∈ b, ∀ c ∈ row, c < 3 := by
  induction b generalizing k with
  | nil => simp
  | cons row rest ih =>
    simp only [rowsOK, Bool.and_eq_true_iff, List.all_eq_true, decide_eq_true_eq] at h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hm
    · exact h.1.2
    · exact ih h.2 r hm

/-- Codes from pairs of adjacent rows, in their geometric order. -/
def stripCodes : Board → List Nat
  | a :: b :: rest => (scanRow a b).map patternKey ++ stripCodes (b :: rest)
  | _ => []

private theorem stripCodes_split (cap : Board) (pivot : List Nat) (tail : Board) :
    stripCodes (cap ++ pivot :: tail) = stripCodes (cap ++ [pivot]) ++ stripCodes (pivot :: tail) := by
  induction cap with
  | nil => simp [stripCodes]
  | cons a as ih =>
    cases as with
    | nil => simp [stripCodes]
    | cons b bs =>
      change _ ++ stripCodes ((b :: bs) ++ pivot :: tail) =
        (_ ++ stripCodes ((b :: bs) ++ [pivot])) ++ _
      rw [ih, List.append_assoc]

private theorem stripCodes_range (b : Board) :
    stripCodes b = (List.range (b.length-1)).flatMap (fun i =>
      (scanRow (b.getD i []) (b.getD (i+1) [])).map patternKey) := by
  induction b with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons d ds =>
      change (scanRow a d).map patternKey ++ stripCodes (d :: ds) = _
      rw [ih]
      simp [List.range_succ_eq_map, List.flatMap_map]

private theorem stripCodes_eq {b : Board} (h : b.length = 10) : stripCodes b = patternCodes b := by
  rw [stripCodes_range, h]
  simp [patternCodes, scanPatterns, List.map_flatMap]

private theorem valid_of_perm {b : Board} (h : WellFormed b)
    (hp : (stripCodes b).Perm (List.range 81)) : Valid b := by
  rw [stripCodes_eq h.1] at hp
  refine ⟨h, ?_⟩
  intro a l m r
  let p : Pattern := (a.val,l.val,m.val,r.val)
  have hc : ColorPattern p := ⟨a.isLt, l.isLt, m.isLt, r.isLt⟩
  have hbound : patternKey p < 81 := by
    have := a.isLt; have := l.isLt; have := m.isLt; have := r.isLt
    simp only [p, patternKey]
    omega
  have he := hp.count_eq (patternKey p)
  rw [List.count_range, ite_eq_left hbound] at he
  rw [patternCodes, h.scanPatterns_eq] at he
  have hm : ((patterns b).map patternKey).count (patternKey p) = (patterns b).count p := by
    simp only [List.count_eq_countP, List.countP_map]
    apply List.countP_congr
    intro q hq
    simp only [Function.comp_apply, beq_iff_eq]
    exact ⟨fun hq' => patternKey_injective (h.pattern_colors hq) hc hq', congrArg patternKey⟩
  exact hm.symm.trans he

/-- Bit `c` records the presence of pattern code `c`. -/
def codeMask : List Nat → Nat
  | [] => 0
  | c :: cs => 2^c ||| codeMask cs

private theorem testBit_mask (cs : List Nat) (n : Nat) :
    (codeMask cs).testBit n = true ↔ n ∈ cs := by
  induction cs with
  | nil => simp [codeMask]
  | cons c cs ih =>
    simp only [codeMask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      ih, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

private theorem codeMask_append (a b : List Nat) :
    codeMask (a ++ b) = codeMask a ||| codeMask b := by
  induction a with
  | nil => simp [codeMask]
  | cons c cs ih => simp [codeMask, ih, Nat.or_assoc]

private theorem perm_of_covered {xs ys : List Nat} (hx : xs.Nodup)
    (hs : xs ⊆ ys) (hl : xs.length = ys.length) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    have hy := List.length_eq_zero_iff.mp hl.symm
    simp [hy]
  | cons a xs ih =>
    obtain ⟨hna, hxs⟩ := List.nodup_cons.mp hx
    have ha := hs List.mem_cons_self
    have hsub : xs ⊆ ys.erase a := by
      intro c hc
      apply (List.mem_erase_of_ne (show c ≠ a from fun h => hna (h ▸ hc))).mpr
      exact hs (List.mem_cons_of_mem a hc)
    have hlen : xs.length = (ys.erase a).length := by
      rw [List.length_erase_of_mem ha, ← hl]
      simp
    exact ((ih hxs hsub hlen).cons a).trans (List.perm_cons_erase ha).symm

/-- Every cap ends directly above the fixed row; every tail starts directly below it. -/
structure Group where
  k : Nat
  pivot : List Nat
  caps : List Board
  tails : List Board
  upperMask : Nat
  lowerMask : Nat

namespace Group

def capOK (g : Group) (cap : Board) : Bool :=
  decide (cap.length = g.k) && rowsOK 0 (cap ++ [g.pivot]) &&
    decide (codeMask (stripCodes (cap ++ [g.pivot])) = g.upperMask)

def tailOK (g : Group) (tail : Board) : Bool :=
  decide (g.k + 1 + tail.length = 10) && rowsOK (g.k+1) tail &&
    decide (codeMask (stripCodes (g.pivot :: tail)) = g.lowerMask)

structure Checked (g : Group) : Prop where
  capCheck : g.caps.all g.capOK = true
  tailCheck : g.tails.all g.tailOK = true
  capsIncreasing : increasing (g.caps.map boardCode) = true
  tailsIncreasing : increasing (g.tails.map boardCode) = true
  complementary : g.upperMask ||| g.lowerMask = 2^81-1

theorem valid {g : Group} (h : g.Checked) {cap tail : Board}
    (hc : cap ∈ g.caps) (ht : tail ∈ g.tails) : Valid (cap ++ g.pivot :: tail) := by
  have hup := List.all_eq_true.mp h.capCheck cap hc
  have hd := List.all_eq_true.mp h.tailCheck tail ht
  simp only [capOK, tailOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hup hd
  have hlen : (cap ++ g.pivot :: tail).length = 10 := by
    simp only [List.length_append, List.length_cons]
    omega
  have hrows : rowsOK 0 (cap ++ g.pivot :: tail) = true := by
    rw [show cap ++ g.pivot :: tail = (cap ++ [g.pivot]) ++ tail by simp]
    rw [rowsOK_append, hup.1.2]
    simpa [hup.1.1] using hd.1.2
  have hw : WellFormed (cap ++ g.pivot :: tail) := by
    refine ⟨hlen, ?_, rowsOK_colors hrows⟩
    intro i hi
    simpa using rowsOK_get hrows (hlen ▸ List.mem_range.mp hi)
  apply valid_of_perm hw
  apply List.Perm.symm
  apply perm_of_covered List.nodup_range
  · intro c hc
    apply (testBit_mask _ c).mp
    rw [stripCodes_split, codeMask_append, hup.2, hd.2, h.complementary, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (List.mem_range.mp hc)
  · rw [stripCodes_eq hlen, patternCodes, hw.scanPatterns_eq, List.length_map, patterns_length]
    decide


def boards (g : Group) : List Board :=
  g.caps.flatMap fun cap => g.tails.map fun tail => cap ++ g.pivot :: tail

def size (g : Group) := g.caps.length * g.tails.length

theorem boards_length (g : Group) : g.boards.length = g.size := by
  simp [boards, size, List.length_flatMap, List.map_const', List.sum_replicate_nat]

theorem cap_length {g : Group} (h : g.Checked) {cap : Board} (hc : cap ∈ g.caps) :
    cap.length = g.k := by
  have he := List.all_eq_true.mp h.capCheck cap hc
  simp only [capOK, Bool.and_eq_true_iff, decide_eq_true_eq] at he
  exact he.1.1

theorem boards_nodup {g : Group} (h : g.Checked) : g.boards.Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro cap _
    exact (nodup_of_increasing_codes h.tailsIncreasing).map _ (by
      intro a b hab he
      exact hab (by simpa using he))
  · apply (nodup_of_increasing_codes h.capsIncreasing).imp_of_mem
    intro ca cb ha hb hne a hma b hmb he
    obtain ⟨ta, _, rfl⟩ := List.mem_map.mp hma
    obtain ⟨tb, _, rfl⟩ := List.mem_map.mp hmb
    have hh := congrArg (List.take g.k) he
    rw [List.take_left' (cap_length h ha), List.take_left' (cap_length h hb)] at hh
    exact hne hh

theorem boards_valid {g : Group} (h : g.Checked) : ∀ b ∈ g.boards, Valid b := by
  intro b hb
  obtain ⟨cap, hc, htail⟩ := List.mem_flatMap.mp hb
  obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp htail
  exact g.valid h hc ht

def signature (g : Group) := (g.pivot, g.upperMask)

private def readSignature (k : Nat) (b : Board) :=
  ((b.drop k).headD [], codeMask (stripCodes (b.take (k+1))))

private theorem signature_of_mem {g : Group} (h : g.Checked) {b : Board} (hb : b ∈ g.boards) :
    readSignature g.k b = g.signature := by
  obtain ⟨cap, hc, htail⟩ := List.mem_flatMap.mp hb
  obtain ⟨tail, _, rfl⟩ := List.mem_map.mp htail
  have he := List.all_eq_true.mp h.capCheck cap hc
  simp only [capOK, Bool.and_eq_true_iff, decide_eq_true_eq] at he
  unfold readSignature signature
  rw [List.drop_left' he.1.1]
  have hlen : (cap ++ [g.pivot]).length = g.k+1 := by simp [he.1.1]
  rw [show cap ++ g.pivot :: tail = (cap ++ [g.pivot]) ++ tail by simp,
    List.take_left' hlen, he.2]
  rfl

/-- A small certificate batch keeps each closed kernel computation bounded.
Its stored integers supply the cheap cross-batch check of strict ordering. -/
structure Batch (check : Board → Bool) where
  values : List Board
  codes : List Nat
  valid : values.all check = true
  fingerprints : values.map boardCode = codes

private theorem batches_valid {check : Board → Bool} (bs : List (Batch check)) :
    (bs.flatMap Batch.values).all check = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [b.valid, ih]

private theorem batches_codes {check : Board → Bool} (bs : List (Batch check)) :
    (bs.flatMap Batch.values).map boardCode = bs.flatMap Batch.codes := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [b.fingerprints, ih]

def assemble (g : Group) (caps : List (Batch g.capOK)) (tails : List (Batch g.tailOK)) : Group :=
  {g with caps := caps.flatMap Batch.values, tails := tails.flatMap Batch.values}

theorem assemble_checked (g : Group) (caps : List (Batch g.capOK)) (tails : List (Batch g.tailOK))
    (hc : increasing (caps.flatMap Batch.codes) = true)
    (ht : increasing (tails.flatMap Batch.codes) = true)
    (h : g.upperMask ||| g.lowerMask = 2^81-1) :
    (assemble g caps tails).Checked := by
  exact ⟨batches_valid caps, batches_valid tails, batches_codes caps ▸ hc, batches_codes tails ▸ ht, h⟩

end Group

theorem groups_nodup (k : Nat) (groups : List Group)
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k)
    (distinct : (groups.map Group.signature).Nodup) : (groups.flatMap Group.boards).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun g hg => g.boards_nodup (checked g hg), ?_⟩
  apply (List.pairwise_map.mp distinct).imp_of_mem
  intro g g' hg hg' hneq b hb b' hb' he
  have h1 := Group.signature_of_mem (checked g hg) hb
  have h2 := Group.signature_of_mem (checked g' hg') hb'
  rw [cut g hg, he] at h1
  rw [cut g' hg'] at h2
  exact hneq (h1.symm.trans h2)

theorem groups_valid {groups : List Group} (checked : ∀ g ∈ groups, g.Checked) :
    ∀ b ∈ groups.flatMap Group.boards, Valid b := by
  intro b hb
  obtain ⟨g, hg, hg'⟩ := List.mem_flatMap.mp hb
  exact g.boards_valid (checked g hg) b hg'

/-- Disjoint splice products at a common cut. A shared row and the codes above
it can be read back from every board, so distinct signatures separate the products. -/
theorem lower_bound (k : Nat) (groups : List Group) (n : Nat)
    (checked : ∀ g ∈ groups, g.Checked)
    (cut : ∀ g ∈ groups, g.k = k)
    (distinct : (groups.map Group.signature).Nodup)
    (count : n ≤ (groups.map Group.size).sum) :
    ∃ f : Fin n → Board, (∀ i, Valid (f i)) ∧ (∀ i j, f i = f j → i = j) := by
  apply injective_family_of_list (groups.flatMap Group.boards) n
  · simpa [List.length_flatMap, Group.boards_length] using count
  · exact groups_nodup k groups checked cut distinct
  · exact groups_valid checked

end TBoards.Splice
