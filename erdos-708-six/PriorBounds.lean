import Slots
import FC4388.Bridge

namespace IntervalSix
open Erdos708Slots

private theorem widen {n k L M : ℕ} (hk : Erdos708.HasCoveringSize n k)
    (A : Finset ℕ) (hc : A.card = n) (ha : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M)
    (hn : 0 < n) (hk' : 0 < k) : Cover L M k (∏ a ∈ A, a) := by
  by_cases hL : 0 < L
  · obtain ⟨B,hB,hc',hd⟩ := hk A hc (fun a h => (ha a h).1) L hL
    have hmax : A.sup id ≤ M := Finset.sup_le fun a h => (ha a h).2
    exact ⟨B,fun a h => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (hB h)).1,
      by have := (Finset.mem_Ico.mp (hB h)).2; omega⟩,hc',hd⟩
  · have hn' : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a,h⟩ := hn'
    obtain ⟨ha1,ha2⟩ := ha a h
    refine ⟨{0}, ?_, by simpa, by simp⟩
    simpa using (show L ≤ 0 ∧ 0 < L+M by omega)

theorem fourCover {L M : ℕ} (A : Finset ℕ) (hA : A.card=4) (ha : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) :
    Cover L M 5 (∏ a ∈ A,a) :=
  widen Erdos708.isLeast_four.1 A hA ha (by decide) (by decide)

theorem fiveCover {L M : ℕ} (A : Finset ℕ) (hA : A.card=5) (ha : ∀ a ∈ A, 2 ≤ a ∧ a ≤ M) :
    Cover L M 6 (∏ a ∈ A,a) :=
  widen Erdos708.isLeast_five.1 A hA ha (by decide) (by decide)

/-- Two fresh multiples extend the five-original cover when one original splits. -/
theorem splitCover {L M a : ℕ} (A : Finset ℕ) (hc : A.card = 6)
    (ha : ∀ b ∈ A, 2 ≤ b ∧ b ≤ M) (ha_mem : a ∈ A)
    (h : ∃ u v : ℕ, 0<u ∧ 0<v ∧ a=u*v ∧ 7*u≤M ∧ 8*v≤M) :
    Cover L M 8 (∏ b ∈ A, b) := by
  obtain ⟨u,v,hu,hv,heq,huM,hvM⟩ := h
  have hcard := Finset.card_erase_add_one ha_mem
  have cov := fiveCover (L := L) (A.erase a) (by omega)
    (fun b hb => ha b (Finset.mem_of_mem_erase hb))
  rw [← A.prod_erase_mul (fun b => b) ha_mem]
  simpa only [← heq] using extend_two cov hu hv huM hvM

end IntervalSix
