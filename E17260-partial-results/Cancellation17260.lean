import Equation17260

namespace Equation17260

variable {α : Type*} {op : α → α → α} (h : Law op)

include h

/-- Applying the law twice lets us move the outer decoder past `x`. -/
private theorem decoder_transport (x z w : α) :
    op z (op x (op z z)) =
      op x (op w (op (op z (op x (op z z))) (op w w))) := by
  calc
    op z (op x (op z z)) =
        op (op (op x x) (op z (op x (op z z))))
          (op w (op (op z (op x (op z z))) (op w w))) :=
      h _ (op x x) w
    _ = _ := by rw [← h x x z]

/-- An idempotent model of Equation 17260 is trivial, even without finiteness. -/
theorem subsingleton_of_idempotent (hi : ∀ x, op x x = x) : Subsingleton α := by
  have right_reset (x y : α) : op (op y x) x = x := by
    simpa only [hi] using (h x y x).symm
  have absorb (x z : α) : op x (op z (op x z)) = x := by
    simpa only [hi] using (h x x z).symm
  have recover_right (x z : α) : op z (op x z) = x := by
    let u := op z (op x z)
    have hu : op x u = x := absorb x z
    calc
      u = op (op x u) u := (right_reset u x).symm
      _ = op x u := congrArg (fun v => op v u) hu
      _ = x := hu
  have right_projection (x y : α) : op x y = y := by
    calc
      op x y = op y (op (op x y) y) := (recover_right (op x y) y).symm
      _ = op y y := by rw [right_reset]
      _ = y := hi y
  refine ⟨fun x y => ?_⟩
  calc
    x = op y (op x y) := (recover_right x y).symm
    _ = y := by rw [right_projection, right_projection]

/-- It is enough that every square is idempotent: the law then makes every
element idempotent, and hence the whole model trivial. -/
theorem subsingleton_of_idempotent_squares
    (hi : ∀ x, op (op x x) (op x x) = op x x) : Subsingleton α := by
  have square_decode (x y : α) : op (op y x) (op x x) = x := by
    have square_absorb := h (op x x) (op x x) x
    simp only [hi] at square_absorb
    have decode := h x y (op x x)
    simpa only [hi, ← square_absorb] using decode.symm
  apply subsingleton_of_idempotent h
  intro x
  simpa only [hi] using square_decode x x

/-- A model of Equation 17260 with even one idempotent is trivial.
No finiteness or cancellation assumption is used. -/
theorem subsingleton_of_one_idempotent (e : α) (he : op e e = e) :
    Subsingleton α := by
  let P : α → α := fun x => op x e
  let Q : α → α := fun x => op e (P x)
  let H : α → α := fun x => op (Q x) x
  -- First, `Q` is a projection whose values are idempotent.
  have recover_e (x y : α) : op (op y x) (Q x) = x := by
    simpa only [Q, P, he] using (h x y e).symm
  have right_twice (x : α) : P (P x) = e := by
    simpa only [Q, P, he] using recover_e e x
  have right_product (x y : α) : P (op y (P x)) = P x := by
    have hq : Q (P x) = e := by dsimp [Q]; rw [right_twice]; exact he
    simpa only [hq, P] using recover_e (P x) y
  have right_project (x : α) : P (Q x) = P x := right_product x e
  have project_twice (x : α) : Q (Q x) = Q x := by dsimp [Q]; rw [right_project]
  have absorb (x : α) : op x (Q x) = Q x := by
    have ht := decoder_transport h x e e
    rw [he] at ht
    change Q x = op x (Q (Q x)) at ht
    simpa only [project_twice] using ht.symm
  have project_idempotent (x : α) : op (Q x) (Q x) = Q x := by
    have ht := recover_e (Q x) x
    simpa only [project_twice, absorb] using ht
  -- Next, every square lies in the image of `Q`.
  have recover_products (x a b : α) : op (op b (op a x)) (H x) = op a x := by
    have ht := h (op a x) b (Q x)
    rw [project_idempotent, recover_e] at ht
    exact ht.symm
  have decoder_product (x z : α) :
      op z (op x (op z z)) = op x (H (op x (op z z))) := by
    have ht := recover_products (op x (op z z)) z (op x x)
    rw [← h x x z] at ht
    exact ht.symm
  have square_projected (x : α) : op x x = Q (op (op x x) (op x x)) := by
    let d := op x x
    let dd := op d d
    have ht := decoder_transport h dd e d
    rw [he] at ht
    change Q dd = op dd (op d (op (Q dd) (op d d))) at ht
    have hs := decoder_product d x
    change op x dd = op d (op (Q dd) dd) at hs
    rw [← hs] at ht
    have heq := h d d x
    change d = op dd (op x dd) at heq
    exact heq.trans ht.symm
  -- Therefore all squares are idempotent, which finishes the proof.
  apply subsingleton_of_idempotent_squares h
  intro x
  have ht := project_idempotent (op (op x x) (op x x))
  rwa [← square_projected x] at ht

/-- Left cancellation is incompatible with a nontrivial model. -/
theorem subsingleton_of_left_cancel
    (hc : ∀ a b c, op a b = op a c → b = c) : Subsingleton α := by
  refine ⟨fun a b => ?_⟩
  let T : α → α := fun x => op a (op x (op a a))
  have decoder_independent (x z : α) : op z (op x (op z z)) = T x := by
    apply hc (op x x)
    exact (h x x z).symm.trans (h x x a)
  have decode_twice (x : α) : T (T x) = op x (op x x) := by
    apply hc x
    have ht := decoder_transport h x a a
    change T x = op x (T (T x)) at ht
    exact ht.symm.trans (decoder_independent x x).symm
  have square_absorb (x : α) : op (T x) (op x x) = op x x := by
    apply hc x
    exact (decoder_independent (T x) x).trans (decode_twice x)
  have decoder_square (x : α) : T x = op (op x x) (T (op x x)) := by
    calc
      T x = op (op x x) (op x (op (op x x) (op x x))) := (decoder_independent x (op x x)).symm
      _ = op (op x x) (T (op x x)) := by rw [decoder_independent (op x x) x]
  have decoder_eq_square (x : α) : T x = op x x := by
    have ht := h (op x x) (T x) a
    change op x x = op (op (T x) (op x x)) (T (op x x)) at ht
    rw [square_absorb] at ht
    exact (decoder_square x).trans ht.symm
  have square_idempotent (x : α) : op (op x x) (op x x) = op x x := by
    simpa only [decoder_eq_square] using square_absorb x
  exact (subsingleton_of_idempotent_squares h square_idempotent).elim a b

/-- Even a square-map cycle of length two forces triviality. -/
theorem subsingleton_of_square_two_cycle (a b : α)
    (hab : op a a = b) (hba : op b b = a) : Subsingleton α := by
  have hab' : op a b = b := by
    simpa only [hab, hba] using (h b b a).symm
  have hba' : b = a := by
    simpa only [hab, hba, hab'] using h b a a
  exact subsingleton_of_one_idempotent h a (hab.trans hba')

/-- Right cancellation is likewise incompatible with a nontrivial model. -/
theorem subsingleton_of_right_cancel
    (hc : ∀ a b c, op b a = op c a → b = c) : Subsingleton α := by
  refine ⟨fun x y => ?_⟩
  apply hc x x y
  apply hc (op x (op x (op x x)))
  exact (h x x x).symm.trans (h x y x)

end Equation17260
