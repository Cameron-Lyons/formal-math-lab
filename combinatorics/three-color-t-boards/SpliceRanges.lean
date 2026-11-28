import SplicePrefixSymmetry

namespace TBoards.Splice

/-- On a repeated signature, a strict gap between the sorted tail lists
makes the two splice products disjoint. -/
def TailSeparated (g h : Group) : Prop :=
  g.signature ≠ h.signature ∨ boardCode (g.tails.getLastD []) < boardCode (h.tails.headD [])

instance (g h : Group) : Decidable (TailSeparated g h) := by
  unfold TailSeparated
  infer_instance

private theorem head_le_mem {xs : List Nat} (h : increasing xs = true) {x : Nat}
    (hx : x ∈ xs) : xs.headD 0 ≤ x := by
  cases xs with
  | nil => simp at hx
  | cons a rest =>
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (increasing_head h x hm)

private theorem mem_le_last {xs : List Nat} (h : increasing xs = true) {x : Nat}
    (hx : x ∈ xs) : x ≤ xs.getLastD 0 := by
  induction xs generalizing x with
  | nil => simp at hx
  | cons a rest ih =>
    cases rest with
    | nil => simp [List.mem_singleton.mp hx]
    | cons b rest =>
      have ht := increasing_tail h
      have hlast : (a :: b :: rest).getLastD 0 = (b :: rest).getLastD 0 := rfl
      rw [hlast]
      rcases List.mem_cons.mp hx with rfl | hm
      · exact Nat.le_trans (Nat.le_of_lt (increasing_head h b (by simp)))
          (ih ht (List.mem_cons_self ..))
      · exact ih ht hm

private theorem tail_mem {g : Group} (h : g.Checked) {b : Board} (hb : b ∈ g.boards) :
    b.drop (g.k+1) ∈ g.tails := by
  obtain ⟨cap, hc, hbs⟩ := List.mem_flatMap.mp hb
  obtain ⟨tail, ht, rfl⟩ := List.mem_map.mp hbs
  have hlen : (cap ++ [g.pivot]).length = g.k+1 := by simp [g.cap_length h hc]
  rwa [show cap ++ g.pivot :: tail = (cap ++ [g.pivot]) ++ tail by simp, List.drop_left' hlen]

theorem groups_nodup_of_separated (k : Nat) (groups : List Group)
    (checked : ∀ g ∈ groups, g.Checked) (cut : ∀ g ∈ groups, g.k = k)
    (separated : groups.Pairwise TailSeparated) : (groups.flatMap Group.boards).Nodup := by
  apply List.pairwise_flatMap.mpr
  refine ⟨fun g hg => g.boards_nodup (checked g hg), ?_⟩
  apply separated.imp_of_mem
  intro g h hg hh hs a ha b hb he
  obtain rfl := he
  rcases hs with hsig | gap
  · have hn := groups_nodup k [g,h] (by simpa using And.intro (checked g hg) (checked h hh))
      (by simpa using And.intro (cut g hg) (cut h hh)) (by simpa using hsig)
    have hn' : (g.boards ++ h.boards).Nodup := by simpa using hn
    exact (List.nodup_append.mp hn').2.2 _ ha _ hb rfl
  · have hta := tail_mem (checked g hg) ha
    have htb := tail_mem (checked h hh) hb
    rw [cut g hg] at hta
    rw [cut h hh] at htb
    have hmax := mem_le_last (checked g hg).tailsIncreasing (List.mem_map_of_mem (f := boardCode) hta)
    have hmin := head_le_mem (checked h hh).tailsIncreasing (List.mem_map_of_mem (f := boardCode) htb)
    change _ ≤ (g.tails.map boardCode).getLastD (boardCode []) at hmax
    change (h.tails.map boardCode).headD (boardCode []) ≤ _ at hmin
    rw [List.getLastD_map] at hmax
    rw [List.headD_map] at hmin
    omega

end TBoards.Splice
