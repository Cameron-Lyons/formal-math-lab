import SpliceSymmetry

/-! Change the shared row of a certified splice family. Only patterns touching
that row must be scanned again. An increasing selection of old tails is encoded
by the numbers of original entries skipped before each selected entry. -/
namespace TBoards.Splice.Transfer

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

private theorem valid_codes_nodup {b : Board} (h : Valid b) : (stripCodes b).Nodup := by
  rw [stripCodes_eq h.1.1, patternCodes, h.1.scanPatterns_eq]
  apply List.pairwise_map.mpr
  have hpatterns : (patterns b).Nodup := by
    apply List.nodup_iff_count_of_mem.mpr
    rintro ⟨a,l,m,r⟩ hm
    obtain ⟨ha,hl,hm',hr⟩ := h.1.pattern_colors hm
    exact h.pattern_count a l m r ha hl hm' hr
  exact hpatterns.imp_of_mem fun ha hb hne he =>
    hne (patternKey_injective (h.1.pattern_colors ha) (h.1.pattern_colors hb) he)

private theorem remove_mask {xs ys : List Nat} (h : (xs ++ ys).Nodup) :
    codeMask (xs ++ ys) ^^^ codeMask xs = codeMask ys := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [codeMask_append, Nat.testBit_xor, Nat.testBit_or]
  cases hx : (codeMask xs).testBit i <;> cases hy : (codeMask ys).testBit i <;> try rfl
  exact False.elim ((List.nodup_append.mp h).2.2 i ((testBit_mask xs i).mp hx)
    i ((testBit_mask ys i).mp hy) rfl)

def boundary (pivot : List Nat) (tail : Board) : Nat :=
  codeMask ((scanRow pivot (tail.headD [])).map patternKey)

private theorem edge_split (pivot : List Nat) (tail : Board) :
    codeMask (stripCodes (pivot :: tail)) = boundary pivot tail ||| codeMask (stripCodes tail) := by
  cases tail with
  | nil => cases pivot <;> simp [stripCodes, boundary, scanRow, codeMask]
  | cons first rest => apply codeMask_append

def compatible (source target : Group) (tail : Board) : Bool :=
  decide (boundary target.pivot tail ||| (source.lowerMask ^^^ boundary source.pivot tail) = target.lowerMask)

private theorem transferred_tail {source target : Group} (hs : source.Checked)
    (sameCut : target.k = source.k) {cap tail : Board} (hcap : cap ∈ source.caps)
    (ht : tail ∈ source.tails) (hc : compatible source target tail = true) :
    target.tailOK tail = true := by
  have hold := List.all_eq_true.mp hs.tailCheck tail ht
  simp only [Group.tailOK, Bool.and_eq_true_iff, decide_eq_true_eq] at hold ⊢
  refine ⟨sameCut ▸ hold.1, ?_⟩
  have hn := valid_codes_nodup (source.valid hs hcap ht)
  rw [stripCodes_split] at hn
  have hn' := (List.nodup_append.mp hn).2.1
  have hr : source.lowerMask ^^^ boundary source.pivot tail = codeMask (stripCodes tail) := by
    rw [← hold.2]
    cases tail with
    | nil => cases source.pivot <;> simp [stripCodes, boundary, scanRow, codeMask]
    | cons first rest => exact remove_mask hn'
  have he := of_decide_eq_true hc
  change boundary target.pivot tail ||| (source.lowerMask ^^^ boundary source.pivot tail) = target.lowerMask at he
  rw [hr] at he
  exact (edge_split _ _).trans he

/-- Skip each indicated number of entries and take the next one. -/
def choose {α : Type} : List Nat → List α → List α
  | [], _ => []
  | gap :: rest, xs =>
    match xs.drop gap with
    | [] => []
    | y :: ys => y :: choose rest ys

theorem choose_sublist {α : Type} (gaps : List Nat) (xs : List α) : (choose gaps xs).Sublist xs := by
  induction gaps generalizing xs with
  | nil => simp [choose]
  | cons gap rest ih =>
    have hs := List.drop_sublist gap xs
    cases he : xs.drop gap with
    | nil => simp [choose, he]
    | cons y ys =>
      rw [he] at hs
      simpa only [choose, he] using ((ih ys).cons_cons y).trans hs

private theorem increasing_iff (xs : List Nat) : increasing xs = true ↔ xs.Pairwise (· < ·) := by
  constructor
  · intro hi
    induction xs with
    | nil => simp
    | cons x xs ih =>
      exact List.pairwise_cons.mpr ⟨increasing_head hi, ih (increasing_tail hi)⟩
  · intro hp
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        apply Bool.and_eq_true_iff.mpr
        exact ⟨decide_eq_true ((List.pairwise_cons.mp hp).1 y List.mem_cons_self),
          ih (List.pairwise_cons.mp hp).2⟩

def assemble (source template : Group) (gaps : List Nat) : Group :=
  {template with tails := choose gaps source.tails}

theorem assemble_checked (source template : Group) (gaps : List Nat) (hs : source.Checked)
    (nonempty : source.caps ≠ []) (sameCut : template.k = source.k)
    (caps : template.caps.all template.capOK = true)
    (capOrder : increasing (template.caps.map boardCode) = true)
    (complete : template.upperMask ||| template.lowerMask = 2^81-1)
    (test : (choose gaps source.tails).all (compatible source template) = true) :
    (assemble source template gaps).Checked := by
  have sub := choose_sublist gaps source.tails
  obtain ⟨cap,hcap⟩ := List.exists_mem_of_ne_nil source.caps nonempty
  refine ⟨caps, ?_, capOrder, ?_, complete⟩
  · apply List.all_eq_true.mpr
    intro t ht
    apply transferred_tail (target := template) hs sameCut hcap (sub.subset ht)
    exact List.all_eq_true.mp test t ht
  · apply (increasing_iff _).mpr
    exact List.Pairwise.sublist (sub.map boardCode) ((increasing_iff _).mp hs.tailsIncreasing)

end TBoards.Splice.Transfer
