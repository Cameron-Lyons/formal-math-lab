import Std

namespace SquareProjection

abbrev Live := List (Nat × Nat)

def survivors (y : Nat) (live : Live) : Live :=
  live.filter (fun tile => y < tile.2)

def arrivals (y : Nat) (news : List Nat) : Live :=
  news.map (fun s => (s, y + s))

def nextLive (y : Nat) (live : Live) (news : List Nat) : Live :=
  survivors y live ++ arrivals y news

/-- At row y the surviving squares continue. Each new square of side s
occupies s rows, including y. Stock records each square exactly once. -/
inductive Reachable : Nat → List Nat → Live → Prop
  | start : Reachable 0 [] []
  | step {y used live} (prior : Reachable y used live) (news : List Nat)
      (sizes : ∀ s ∈ news, 1 ≤ s ∧ s ≤ 21)
      (count : (nextLive y live news).length = 3)
      (width : ((nextLive y live news).map Prod.fst).sum = 43)
      (stock : ∀ s ∈ news, (used ++ news).count s ≤ 2) :
      Reachable (y+1) (used ++ news) (nextLive y live news)

private def menus : Nat → Nat → List (List Nat)
  | 0, w => if w = 0 then [[]] else []
  | k+1, w => (List.range (min 21 w)).flatMap fun i =>
      (menus k (w - (i+1))).map fun rest => (i+1) :: rest

private theorem mem_menus (news : List Nat)
    (sizes : ∀ s ∈ news, 1 ≤ s ∧ s ≤ 21) :
    news ∈ menus news.length news.sum := by
  induction news with
  | nil => simp [menus]
  | cons s tail ih =>
    have hs := sizes s (by simp)
    have ht := ih (fun t ht => sizes t (by simp [ht]))
    simp only [List.length_cons, List.sum_cons, menus, List.mem_flatMap,
      List.mem_range, List.mem_map]
    refine ⟨s-1, by omega, tail, ?_, ?_⟩
    · simpa [show s - 1 + 1 = s by omega] using ht
    · simp [show s - 1 + 1 = s by omega]

private def search : Nat → Nat → List Nat → Live → Bool
  | 0, _, _, _ => true
  | n+1, y, used, live =>
    let keep := survivors y live
    let width := (keep.map Prod.fst).sum
    (menus (3-keep.length) (43-width)).any fun news =>
      (news.all fun s => (used ++ news).count s ≤ 2) &&
      search n (y+1) (used ++ news) (keep ++ arrivals y news)

private theorem step_search {fuel y used live news}
    (sizes : ∀ s ∈ news, 1 ≤ s ∧ s ≤ 21)
    (count : (nextLive y live news).length = 3)
    (width : ((nextLive y live news).map Prod.fst).sum = 43)
    (stock : ∀ s ∈ news, (used ++ news).count s ≤ 2)
    (accept : search fuel (y+1) (used ++ news) (nextLive y live news) = true) :
    search (fuel+1) y used live = true := by
  have c : (survivors y live).length + news.length = 3 := by
    simpa [nextLive, arrivals] using count
  have w : ((survivors y live).map Prod.fst).sum + news.sum = 43 := by
    simpa [nextLive, arrivals, Function.comp_def] using width
  simp only [search, List.any_eq_true]
  refine ⟨news, ?_, ?_⟩
  · simpa [show 3 - (survivors y live).length = news.length by omega,
      show 43 - ((survivors y live).map Prod.fst).sum = news.sum by omega]
      using mem_menus news sizes
  · simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    exact ⟨stock, accept⟩

private theorem empty_search : search 154 0 [] [] = false := by native_decide

private theorem search_fails {y used live} (t : Reachable y used live) (bound : y ≤ 154) :
    search (154-y) y used live = false := by
  induction t with
  | start => exact empty_search
  | @step y used live prior news sizes count width stock ih =>
    have pre := ih (by omega)
    cases success : search (154 - (y+1)) (y+1) (used ++ news) (nextLive y live news) with
    | false => rfl
    | true =>
      have yes := step_search sizes count width stock success
      have eq : 154 - (y + 1) + 1 = 154-y := by omega
      rw [eq, pre] at yes
      contradiction

theorem no_projection_43 (used : List Nat) (live : Live) : ¬ Reachable 154 used live := by
  intro h
  have bad := search_fails h (by decide)
  exact Bool.noConfusion bad

end SquareProjection
