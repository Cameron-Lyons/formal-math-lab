import Ramsey39

/-!
# CertVerify.lean
Pure-kernel branch-and-bound + edge/singleton clique-cover certificate verifier
compatible with `Ramsey310.Simple`, `Ramsey310.TriangleFree`, `Ramsey310.Independent`,
and `Ramsey310.orderOf`.
-/

namespace Ramsey310.Cert

/-- Independence predicate on a list of vertices. -/
def IsIndep {n : Nat} (edge : Fin n → Fin n → Bool) (S : List (Fin n)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, edge u v = false

/-- Branch-and-bound + edge/singleton clique-cover certificate tree proving
    that no independent set inside `avail` has size at least `k`. -/
inductive CertTree (n : Nat) where
  | cover (edges : List (Fin n × Fin n)) (singles : List (Fin n)) : CertTree n
  | branch (v : Fin n) (withV : CertTree n) (withoutV : CertTree n) : CertTree n
  deriving Repr

/-- Boolean checker for whether `x` is covered by `edges` or `singles`. -/
def isCovered {n : Nat} (edges : List (Fin n × Fin n)) (singles : List (Fin n)) (x : Fin n) : Bool :=
  singles.any (· == x) || edges.any (fun p => p.1 == x || p.2 == x)

/-- Pure-kernel Boolean certificate verifier. -/
def checkCert {n : Nat} (edge : Fin n → Fin n → Bool) :
    List (Fin n) → Nat → CertTree n → Bool
  | avail, k, .cover edges singles =>
      decide (edges.length + singles.length < k) &&
      edges.all (fun p => edge p.1 p.2) &&
      avail.all (isCovered edges singles)
  | avail, k, .branch v withV withoutV =>
      match k with
      | 0 => false
      | k' + 1 =>
          checkCert edge (avail.filter (fun x => x != v && !(edge v x))) k' withV &&
          checkCert edge (avail.filter (fun x => x != v)) (k' + 1) withoutV

private theorem nodup_map_of_inj {α β : Type} {f : α → β} (hinj : ∀ a b, f a = f b → a = b) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
      have ⟨hna, hnt⟩ := List.nodup_cons.mp h
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, nodup_map_of_inj hinj hnt⟩
      obtain ⟨b, hb, hba⟩ := List.mem_map.mp hm
      exact hna (hinj b a hba ▸ hb)

/-- Each edge in `edges` contains at most one vertex of an independent set `S`,
    and each element of `singles` covers at most one vertex, so `|S| ≤ |edges| + |singles|`. -/
theorem indep_length_le_cover {n : Nat} {edge : Fin n → Fin n → Bool}
    (edges : List (Fin n × Fin n)) (singles : List (Fin n)) (S : List (Fin n))
    (hnd : S.Nodup) (hind : IsIndep edge S)
    (hedges : ∀ p ∈ edges, edge p.1 p.2 = true)
    (hcov : ∀ x ∈ S, x ∈ singles ∨ ∃ p ∈ edges, p.1 = x ∨ p.2 = x) :
    S.length ≤ edges.length + singles.length := by
  induction edges generalizing S with
  | nil =>
      have hsub : ∀ x ∈ S, x ∈ singles := fun x hx =>
        (hcov x hx).elim id (fun ⟨_, hp, _⟩ => nomatch hp)
      simpa using List.Nodup.length_le_of_subset hnd hsub
  | cons e es ih =>
      let S' := (S.erase e.1).erase e.2
      have hnotboth : ¬ (e.1 ∈ S ∧ e.2 ∈ S) := fun ⟨h1, h2⟩ => by
        have := hind e.1 h1 e.2 h2
        rw [hedges e List.mem_cons_self] at this; contradiction
      have hlen_step : S.length ≤ S'.length + 1 := by
        dsimp [S']
        by_cases h1 : e.1 ∈ S
        · have h2 : e.2 ∉ S.erase e.1 := fun hm => hnotboth ⟨h1, List.mem_of_mem_erase hm⟩
          rw [List.erase_of_not_mem h2, List.length_erase_of_mem h1]
          have := List.length_pos_of_mem h1; omega
        · rw [List.erase_of_not_mem h1]
          by_cases h2 : e.2 ∈ S
          · rw [List.length_erase_of_mem h2]; have := List.length_pos_of_mem h2; omega
          · rw [List.erase_of_not_mem h2]; omega
      have hmemS : ∀ x ∈ S', x ∈ S := fun x hx =>
        List.mem_of_mem_erase (List.mem_of_mem_erase hx)
      have hnd1 : (S.erase e.1).Nodup := List.Nodup.erase e.1 hnd
      have hcov' : ∀ x ∈ S', x ∈ singles ∨ ∃ p ∈ es, p.1 = x ∨ p.2 = x := by
        intro x hx
        have hne2 : x ≠ e.2 := fun h => (List.Nodup.not_mem_erase hnd1) (h ▸ hx)
        have hne1 : x ≠ e.1 := fun h => (List.Nodup.not_mem_erase hnd) (h ▸ List.mem_of_mem_erase hx)
        cases hcov x (hmemS x hx) with
        | inl hs => exact Or.inl hs
        | inr hex =>
            obtain ⟨p, hp, hpx⟩ := hex
            cases hp with
            | head => cases hpx with
              | inl h => exact absurd h.symm hne1
              | inr h => exact absurd h.symm hne2
            | tail _ hpt => exact Or.inr ⟨p, hpt, hpx⟩
      have iht := ih S' (List.Nodup.erase e.2 hnd1)
        (fun u hu v hv => hind u (hmemS u hu) v (hmemS v hv))
        (fun p hp => hedges p (List.mem_cons_of_mem e hp)) hcov'
      simp only [List.length_cons]; omega

theorem checkCert_sound {n : Nat} {edge : Fin n → Fin n → Bool} (cert : CertTree n) :
    ∀ (avail : List (Fin n)) (k : Nat),
      checkCert edge avail k cert = true →
      ∀ (S : List (Fin n)), S.Nodup → (∀ x ∈ S, x ∈ avail) → IsIndep edge S → S.length < k := by
  induction cert with
  | cover edges singles =>
      intro avail k hchk S hnd hsub hind
      simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
      obtain ⟨⟨hlt, hedges⟩, hcovAvail⟩ := hchk
      have hcovS : ∀ x ∈ S, x ∈ singles ∨ ∃ p ∈ edges, p.1 = x ∨ p.2 = x := by
        intro x hx
        have hbx := hcovAvail x (hsub x hx)
        simp only [isCovered, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hbx
        exact hbx.elim (fun ⟨w, hw, hwx⟩ => Or.inl (hwx ▸ hw))
          (fun ⟨p, hp, hpx⟩ => Or.inr ⟨p, hp, hpx⟩)
      have := indep_length_le_cover edges singles S hnd hind hedges hcovS
      omega
  | branch v withV withoutV ihWith ihWithout =>
      intro avail k hchk S hnd hsub hind
      cases k with
      | zero => simp [checkCert] at hchk
      | succ k' =>
          simp only [checkCert, Bool.and_eq_true] at hchk
          by_cases hv : v ∈ S
          · let S' := S.erase v
            have hsub' : ∀ x ∈ S', x ∈ avail.filter (fun x => x != v && !(edge v x)) := by
              intro x hx
              have hxS := List.mem_of_mem_erase hx
              have hne : x ≠ v := fun h => (List.Nodup.not_mem_erase hnd) (h ▸ hx)
              exact List.mem_filter.mpr ⟨hsub x hxS, by simp [hne, hind v hv x hxS]⟩
            have hlt' := ihWith _ k' hchk.1 S' (List.Nodup.erase v hnd) hsub'
              (fun u hu w hw => hind u (List.mem_of_mem_erase hu) w (List.mem_of_mem_erase hw))
            have hlen : S'.length = S.length - 1 := List.length_erase_of_mem hv
            have hpos := List.length_pos_of_mem hv
            omega
          · have hsub' : ∀ x ∈ S, x ∈ avail.filter (fun x => x != v) := fun x hx =>
              List.mem_filter.mpr ⟨hsub x hx, by simp [show x ≠ v from fun h => hv (h ▸ hx)]⟩
            exact ihWithout _ (k' + 1) hchk.2 S hnd hsub' hind

/-- Decidable check for `Simple` and `TriangleFree` on `Fin n`. -/
def checkSimpleTriFree {n : Nat} (edge : Fin n → Fin n → Bool) : Bool :=
  (List.finRange n).all (fun u => !(edge u u)) &&
  (List.finRange n).all (fun u => (List.finRange n).all (fun v => edge u v == edge v u)) &&
  (List.finRange n).all (fun u => (List.finRange n).all (fun v =>
    !(edge u v) || (List.finRange n).all (fun w => !(edge v w) || !(edge w u))))

theorem simpleTriFree_of_check {n : Nat} {edge : Fin n → Fin n → Bool}
    (htf : checkSimpleTriFree edge = true) :
    Simple edge ∧ TriangleFree edge := by
  simp only [checkSimpleTriFree, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    Bool.or_eq_true, beq_iff_eq] at htf
  obtain ⟨⟨hirr, hsymm⟩, htri⟩ := htf
  refine ⟨⟨fun u => hirr u (List.mem_finRange u),
           fun u v => hsymm u (List.mem_finRange u) v (List.mem_finRange v)⟩,
          fun u v w huv hvw => ?_⟩
  rcases htri u (List.mem_finRange u) v (List.mem_finRange v) with h | h2
  · rw [huv] at h; contradiction
  · rcases h2 w (List.mem_finRange w) with h | h
    · rw [hvw] at h; contradiction
    · exact h

/-- Soundness bridge to `Ramsey310.orderOf`: a verified certificate rules out independent `k`-sets. -/
theorem orderOf_lt_of_checkCert {n k : Nat} {edge : Fin n → Fin n → Bool}
    (cert : CertTree n) (hchk : checkCert edge (List.finRange n) k cert = true)
    (s : Fin n → Bool) (hind : Independent edge s) : orderOf s < k :=
  checkCert_sound cert (List.finRange n) k hchk ((List.finRange n).filter s)
    ((List.nodup_finRange n).filter s)
    (fun x _ => List.mem_finRange x)
    (fun u hu v hv => hind u v (List.mem_filter.mp hu).2 (List.mem_filter.mp hv).2)

/-- Vertex-transitive optimization for circulant graphs: checking `V \ N[0]` for bound `k`
    proves `orderOf s < k + 1` for every independent set `s`. -/
theorem orderOf_lt_of_circulant_checkCert {n k : Nat} {edge : Fin n → Fin n → Bool}
    (hn : 0 < n)
    (hshift : ∀ (shift u v : Fin n),
      edge ⟨(u.val + shift.val) % n, Nat.mod_lt _ hn⟩
           ⟨(v.val + shift.val) % n, Nat.mod_lt _ hn⟩ = edge u v)
    (cert : CertTree n)
    (hchk : checkCert edge ((List.finRange n).filter (fun x => x.val != 0 && !(edge ⟨0, hn⟩ x))) k cert = true)
    (s : Fin n → Bool) (hind : Independent edge s) : orderOf s < k + 1 := by
  let S := (List.finRange n).filter s
  cases hS : S with
  | nil =>
      change S.length < k + 1
      rw [hS]; exact Nat.zero_lt_succ k
  | cons v0 rest =>
      have hv0 : v0 ∈ S := hS ▸ List.mem_cons_self
      let shift : Fin n := ⟨(n - v0.val) % n, Nat.mod_lt _ hn⟩
      let rot (x : Fin n) : Fin n := ⟨(x.val + shift.val) % n, Nat.mod_lt _ hn⟩
      have hrot_inj : ∀ a b, rot a = rot b → a = b := by
        intro a b hab
        apply Fin.ext
        have hmod : (a.val + shift.val) % n = (b.val + shift.val) % n := congrArg Fin.val hab
        have ha := a.isLt; have hb := b.isLt; have hs := shift.isLt
        have hwrap : ∀ x < n, (x + shift.val) % n = if x + shift.val < n then x + shift.val else x + shift.val - n := by
          intro x hx; split
          · exact Nat.mod_eq_of_lt ‹_›
          · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        rw [hwrap _ ha, hwrap _ hb] at hmod; split at hmod <;> split at hmod <;> omega
      have hrot0 : rot v0 = ⟨0, hn⟩ := Fin.ext (by
        show (v0.val + (n - v0.val) % n) % n = 0
        have hv := v0.isLt
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_sub_of_le (Nat.le_of_lt hv), Nat.mod_self])
      let T := S.map rot
      have hTnd : T.Nodup := nodup_map_of_inj hrot_inj ((List.nodup_finRange n).filter s)
      have hT0 : (⟨0, hn⟩ : Fin n) ∈ T := List.mem_map.mpr ⟨v0, hv0, hrot0⟩
      have hTind : IsIndep edge T := by
        intro u hu v hv
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hu
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hv
        exact (hshift shift a b).trans (hind a b (List.mem_filter.mp ha).2 (List.mem_filter.mp hb).2)
      let T' := T.erase ⟨0, hn⟩
      have hsub : ∀ x ∈ T', x ∈ (List.finRange n).filter (fun x => x.val != 0 && !(edge ⟨0, hn⟩ x)) := by
        intro x hx
        have hxT := List.mem_of_mem_erase hx
        have hne : x ≠ ⟨0, hn⟩ := fun h => (List.Nodup.not_mem_erase hTnd) (h ▸ hx)
        have hne0 : x.val ≠ 0 := fun h0 => hne (Fin.ext h0)
        exact List.mem_filter.mpr ⟨List.mem_finRange x, by simp [hne0, hTind ⟨0, hn⟩ hT0 x hxT]⟩
      have hlt := checkCert_sound cert _ k hchk T' (List.Nodup.erase _ hTnd) hsub
        (fun u hu v hv => hTind u (List.mem_of_mem_erase hu) v (List.mem_of_mem_erase hv))
      have hlen : T'.length = S.length - 1 := by
        rw [List.length_erase_of_mem hT0, List.length_map]
      have hpos : 0 < S.length := by rw [hS]; exact Nat.zero_lt_succ _
      change S.length < k + 1
      omega

end Ramsey310.Cert
