import StripCertificates

namespace Grid75

/-- An unrestricted 150-point solution cannot retain every seed point outside
a band of 32 consecutive original rows. It may place points anywhere on the
75 × 75 grid, including the formerly empty row. -/
theorem no_32_row_repair (first : Fin 43) {s : List Point}
    (keep : ∀ p ∈ witness148, p.2.val < first.val ∨ first.val + 32 ≤ p.2.val → p ∈ s)
    (nd : s.Nodup) (nt : NoThree s) : s.length ≠ 150 := by
  refine StripSearch.strip_sound (first := first.val) (width := 32)
    (StripSearch.certificates first) ?_ nd nt
  intro p hp
  have mem : p ∈ witness148.filter (fun q => decide
      (q.2.val < first.val ∨ first.val + 32 ≤ q.2.val)) := by
    simpa [StripSearch.retained] using hp
  obtain ⟨hs, outside⟩ := List.mem_filter.mp mem
  exact keep p hs (of_decide_eq_true outside)

/-- Any 150-point solution omits two points of the published 148-point
placement whose row indices differ by at least 32. -/
theorem omitted_rows_separated {s : List Point} (size : s.length = 150)
    (nd : s.Nodup) (nt : NoThree s) :
    ∃ p ∈ witness148, p ∉ s ∧ ∃ q ∈ witness148, q ∉ s ∧ p.2.val + 32 ≤ q.2.val := by
  classical
  let omitted := witness148.filter fun p => decide (p ∉ s)
  have escape (a : Fin 43) : ∃ q ∈ omitted, q.2.val < a.val ∨ a.val + 32 ≤ q.2.val := by
    apply Classical.byContradiction
    intro none
    apply no_32_row_repair a _ nd nt size
    intro q hq out
    exact Classical.byContradiction fun miss =>
      none ⟨q, List.mem_filter.mpr ⟨hq, by simpa using miss⟩, out⟩
  obtain ⟨u, hu, _⟩ := escape 0
  let row := fun p : Point => p.2.val
  have nonempty := List.ne_nil_of_mem hu
  let p := omitted.minOn row nonempty
  have hp : p ∈ omitted := List.minOn_mem
  let a : Fin 43 := ⟨min (row p) 42, by omega⟩
  obtain ⟨q, hq, outside⟩ := escape a
  have least : row p ≤ row q := List.apply_minOn_le_of_mem hq
  obtain ⟨ps, pm⟩ := List.mem_filter.mp hp
  obtain ⟨qs, qm⟩ := List.mem_filter.mp hq
  have rows : ∀ r ∈ witness148, r.2.val < 74 := by
    set_option maxRecDepth 10000 in decide +kernel
  have bound := rows q qs
  refine ⟨p, ps, of_decide_eq_true pm, q, qs, of_decide_eq_true qm, ?_⟩
  change q.2.val < min p.2.val 42 ∨ min p.2.val 42 + 32 ≤ q.2.val at outside
  change p.2.val ≤ q.2.val at least
  omega

end Grid75
