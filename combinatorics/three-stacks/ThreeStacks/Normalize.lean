import ThreeStacks.Machine
import ThreeStacks.Lower

namespace ThreeStacks

private def stackView (x : Nat) (s : List Nat) := s.filter fun a => decide (a ≠ 1 ∧ a ≠ x)
private def inputView (x : Nat) (i : List Nat) := i.filterMap fun a =>
  if a = 1 then none else some (if a = x then 1 else a)
private def outputView (o : List Nat) := o.filter fun a => decide (a ≠ 1)

/-- Before the last input 1 is consumed, no card can be output. -/
private def Gated (i s t u o : List Nat) : Prop :=
  i ≠ [] → i.getLast? = some 1 ∧ o.head? = some 1 ∧ 1 ∉ s ∧ 1 ∉ t ∧ 1 ∉ u

private theorem bypass (r : Run i s t u o) (x : Nat) : Run (x::i) s t u (x::o) :=
  .input (.first (.second (.output r)))

/-- Erase operations on 1 and x. Instead bypass 1 at the old input of x,
    and bypass the new final x at the old output of x. The ordinary cards
    remain in exactly their old order at each stack and at both terminals. -/
private theorem runSwap {i s t u o : List Nat} (r : Run i s t u o) (x : Nat) (hx : x ≠ 1)
    (ni : i.Nodup) (no : o.Nodup) (gate : Gated i s t u o) :
    Run (inputView x i ++ (if x ∈ o then [x] else []))
      (stackView x s) (stackView x t) (stackView x u)
      ((if x ∈ i then [1] else []) ++ outputView o) := by
  induction r with
  | done => simpa [inputView, stackView, outputView] using Run.done
  | @input i a s t u o _ ih =>
    have htail := List.nodup_cons.mp ni
    have g' : Gated i (a::s) t u o := by
      intro hn
      obtain ⟨last, head, s1,t1,u1⟩ := gate (List.cons_ne_nil _ _)
      rw [List.getLast?_cons_of_ne_nil hn] at last
      have am : a ≠ 1 := fun e => htail.1 (e ▸ List.mem_of_getLast? last)
      exact ⟨last,head,by simp [Ne.symm am,s1],t1,u1⟩
    have h := ih htail.2 no g'
    by_cases one : a = 1
    · subst a
      simpa [inputView,stackView,hx] using h
    by_cases ax : a = x
    · subst a
      have notin := htail.1
      simpa [inputView,stackView,hx,notin] using bypass h 1
    · simp [inputView,stackView,one,ax,Ne.symm ax] at h ⊢
      exact .input h
  | @first i s a t u o _ ih =>
    have g' : Gated i s (a::t) u o := by
      intro hn
      obtain ⟨last,head,h,t1,u1⟩ := gate hn
      simp at h
      exact ⟨last,head,h.2,by simp [h.1,t1],u1⟩
    have h := ih ni no g'
    by_cases elim : a = 1 ∨ a = x
    · rcases elim with h1|h1 <;> subst a <;> simpa [stackView] using h
    · have h1 : a ≠ 1 := fun e => elim (.inl e)
      have h2 : a ≠ x := fun e => elim (.inr e)
      simp [stackView,h1,h2] at h ⊢
      exact .first h
  | @second i s t a u o _ ih =>
    have g' : Gated i s t (a::u) o := by
      intro hn
      obtain ⟨last,head,s1,h,u1⟩ := gate hn
      simp at h
      exact ⟨last,head,s1,h.2,by simp [h.1,u1]⟩
    have h := ih ni no g'
    by_cases elim : a = 1 ∨ a = x
    · rcases elim with h1|h1 <;> subst a <;> simpa [stackView] using h
    · have h1 : a ≠ 1 := fun e => elim (.inl e)
      have h2 : a ≠ x := fun e => elim (.inr e)
      simp [stackView,h1,h2] at h ⊢
      exact .second h
  | @output i s t u o a _ ih =>
    have empty : i = [] := by
      by_cases hn : i = []
      · exact hn
      apply False.elim
      obtain ⟨_,head,_,_,h⟩ := gate hn
      simp only [List.head?_cons,Option.some.injEq] at head
      exact h (by simp [head])
    subst i
    have h := ih ni (List.nodup_cons.mp no).2 (by intro hn; exact (hn rfl).elim)
    by_cases one : a = 1
    · subst a
      simpa [inputView,stackView,outputView,hx] using h
    by_cases ax : a = x
    · subst a
      have notin := (List.nodup_cons.mp no).1
      simpa [inputView,stackView,outputView,hx,notin] using bypass h x
    · simp [inputView,stackView,outputView,one,ax,Ne.symm ax] at h ⊢
      exact .output h

private theorem inputView_clear (x : Nat) (l : List Nat) (h₁ : 1 ∉ l) (hₓ : x ∉ l) :
    inputView x l = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp at h₁ hₓ
    have h := ih h₁.2 hₓ.2
    simpa [inputView,Ne.symm h₁.1,Ne.symm hₓ.1] using congrArg (List.cons a) h

/-- Given a sorting of the order with final 1, restore 1 to its old input
    position and restore that position's card x to the very end of the input. -/
theorem endSwap (l r out : List Nat) (x : Nat) (hx : x ≠ 1)
    (hi : (l ++ x :: (r ++ [1])).Nodup) (ho : (1 :: out).Nodup) (xo : x ∈ out)
    (sort : SortsTo (l ++ x :: (r ++ [1])) (1 :: out)) :
    SortsTo (l ++ 1 :: (r ++ [x])) (1 :: out) := by
  have gated : Gated (l ++ x :: (r ++ [1])) [] [] [] (1::out) := by
    intro _
    exact ⟨List.getLast?_eq_some_iff.mpr ⟨l ++ x::r, by simp⟩,rfl,by simp,by simp,by simp⟩
  have run := runSwap ((run_iff_sortsTo _ _).mpr sort) x hx hi ho gated
  obtain ⟨_,hr,cross⟩ := List.nodup_append.mp hi
  have ul : 1 ∉ l := fun h => cross 1 h 1 (by simp) rfl
  have xl : x ∉ l := fun h => cross x h x (by simp) rfl
  obtain ⟨xn,rn⟩ := List.nodup_cons.mp hr
  obtain ⟨_,_,crossr⟩ := List.nodup_append.mp rn
  have ur : 1 ∉ r := fun h => crossr 1 h 1 (by simp) rfl
  have xr : x ∉ r := fun h => xn (List.mem_append_left _ h)
  have clean : outputView out = out := by
    apply List.filter_eq_self.mpr
    intro a ha
    exact decide_eq_true (fun e => (List.nodup_cons.mp ho).1 (e ▸ ha))
  have input_ok : inputView x (l ++ x :: (r++[1])) = l ++ 1::r := by
    have vl := inputView_clear x l ul xl
    have vr := inputView_clear x r ur xr
    simp only [inputView] at vl vr ⊢
    simp [vl,vr,hx]
  have output_ok : outputView (1::out) = out := by simpa [outputView] using clean
  apply (run_iff_sortsTo _ _).mp
  simpa [input_ok,output_ok,stackView,xo] using run

/-- Normalized exhaustive evidence, covering decks ending in 1, suffices for
    an arbitrary positive length. -/
theorem allFromEndingOne (n : Nat)
    (h : ∀ q, IsDeck (n+1) q → q.getLast? = some 1 → Sortable (n+1) q)
    (p : List Nat) (hp : IsDeck (n+1) p) : Sortable (n+1) p := by
  have out : target (n+1) = 1 :: List.range' 2 n := rfl
  cases e : p.getLast? with
  | none =>
    have empty := List.getLast?_eq_none_iff.mp e
    have len := hp.length_eq
    simp [empty,target] at len
  | some x =>
    by_cases hx : x = 1
    · exact h p hp (hx ▸ e)
    obtain ⟨z, rfl⟩ := List.getLast?_eq_some_iff.mp e
    have hm : 1 ∈ z ++ [x] := hp.mem_iff.mpr (by simp [out])
    have h1 : 1 ∈ z := by simpa [Ne.symm hx] using hm
    obtain ⟨l,r,rfl⟩ := List.mem_iff_append.mp h1
    have exchange : (l ++ x :: (r++[1])).Perm ((l++1::r)++[x]) := by
      rw [List.append_assoc]
      apply List.Perm.append_left
      exact (List.perm_append_singleton 1 (x::r)).trans ((List.perm_append_singleton x r).symm.cons 1)
    have qp : IsDeck (n+1) (l++x::(r++[1])) := exchange.trans hp
    have last : (l ++ x::(r++[1])).getLast? = some 1 :=
      List.getLast?_eq_some_iff.mpr ⟨l++x::r,by simp⟩
    have sorted := h _ qp last
    have nd : (target (n+1)).Nodup := List.nodup_range' 1
    have xm : x ∈ target (n+1) := qp.mem_iff.mp (by simp)
    rw [out] at xm nd
    have xo : x ∈ List.range' 2 n := by simpa [hx] using xm
    change SortsTo _ (target (n+1)) at sorted ⊢
    rw [out] at sorted ⊢
    exact List.append_assoc l (1::r) [x] ▸ endSwap l r _ x hx (qp.nodup_iff.mpr (by rw [out];exact nd)) nd xo sorted

/-- The effective length-19 certificate premise only concerns permutations ending in 1. -/
theorem allShorterFromNormalized
    (h19 : ∀ p, IsDeck 19 p → p.getLast? = some 1 → Sortable 19 p) :
    ∀ n, n ≤ 19 → ∀ p, IsDeck n p → Sortable n p :=
  allShorter (allFromEndingOne 18 h19)

end ThreeStacks
