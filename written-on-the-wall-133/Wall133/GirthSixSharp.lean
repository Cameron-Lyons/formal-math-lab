import Wall133.GirthSixDensity
import Wall133.CoreExterior
import Wall133.CoreIncidence

/-! # Sharp even thresholds at girth six

At a stalled induced path the used contact indices are at least two apart.
When the geodesic extension is short, all three available slots on its
original segment are occupied, each by a private neighbor. A rotation
returns the endpoint to the core near the original anchor. The argument
also handles a shortest path with a core edge prepended between vertices
in the same distance layer. This allows counting the high-degree neighbors
of every core vertex without a coloring.
-/

namespace Wall133
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {n : ℕ}

private lemma realize_chain (P : Chain G n) :
    ∃ p : G.Walk (P.vertex 0) (P.vertex n), p.length=n ∧ Chordless p ∧
      ∀ i ≤ n, p.getVert i=P.vertex i := by
  have build (m : ℕ) (f : ℕ → V) (adj : ∀ i < m,G.Adj (f i) (f (i+1))) :
      ∃ p : G.Walk (f 0) (f m), p.length=m ∧ ∀ i ≤ m,p.getVert i=f i := by
    induction m generalizing f with
    | zero => exact ⟨.nil,rfl,by simp⟩
    | succ m ih =>
      obtain ⟨p,hp,hv⟩ := ih (fun i => f (i+1)) (fun i hi => adj (i+1) (by omega))
      refine ⟨p.cons (adj 0 (by omega)),by simp [hp],?_⟩
      rintro (_|i) hi
      · rfl
      · exact hv i (by omega)
  obtain ⟨p,hp,hv⟩ := build n P.vertex (fun i hi => (P.edges (by omega) (by omega)).2 (Or.inl rfl))
  refine ⟨p,hp,⟨?_,?_⟩,hv⟩
  · rw [p.isPath_iff_injective_get_support,←p.getVert_comp_val_eq_get_support]
    intro i j e
    have hi := i.isLt; have hj := j.isLt
    have hs := p.length_support
    change p.getVert i.val=p.getVert j.val at e
    rw [hv _ (by omega),hv _ (by omega)] at e
    exact Fin.ext (P.inj (by omega) (by omega) e)
  · intro i j hi hj h
    rw [hp] at hi hj
    rw [hv _ hi,hv _ hj] at h
    exact (P.edges hi hj).1 h

private theorem no_short_triangle (hg : 6 ≤ G.egirth) {a b z : V}
    (hab : G.Adj a b) (haz : G.Adj a z) (hbz : G.Adj b z) : False := by
  let p := hab.toWalk
  have len : p.length=1 := rfl
  have hgeo : p.length=G.dist a b := len.trans (dist_eq_one_iff_adj.mpr hab).symm
  have hp : Chordless p := ⟨p.isPath_of_length_eq_dist hgeo,
    fun i j hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist p hgeo hi hj).1⟩
  have off : z ∉ p.support := by simp [p,Adj.toWalk,haz.ne.symm,hbz.ne.symm]
  have h := first_blocker (g:=6) hg hp haz off (show 1 ≤ p.length from len.ge) (by decide)
    (show G.Adj z (p.getVert 1) from hbz.symm)
  omega

private structure Contacts (P : Chain G n) (N : Finset V) where
  -- A contact is a positive index where an unused neighbor meets the chain.
  touches (w : N) (i : ℕ) : Prop
  exists_site (w : N) : ∃ i, touches w i
  adjacent {w i} : touches w i → G.Adj (P.vertex i) w.val
  iff_adj {w i} (hi : i ≤ n) (hpos : i ≠ 0) : touches w i ↔ G.Adj (P.vertex i) w.val
  lower {w i} : touches w i → 4 ≤ i
  upper {w i} : touches w i → i ≤ n
  separate {w z i j} : touches w i → touches z j → i ≤ j → w ≠ z ∨ i ≠ j → i+2 ≤ j

open scoped Classical in
private noncomputable def contacts_of_stall (P : Chain G n) (hn : 1 ≤ n) (hg : 6 ≤ G.egirth) (N : Finset V)
    (adj : ∀ w∈N,G.Adj (P.vertex 0) w) (avoid : ∀ w∈N,w ≠ P.vertex 1)
    (sat : ∀ w∈N,¬Good P w) : Contacts P N := by
  apply Classical.choice
  obtain ⟨p,hlen,hp,idx⟩ := realize_chain P
  have off (w : N) : w.val ∉ p.support := hp.pending_off_path (adj w w.property) (by
    intro he
    exact avoid w w.property (he.trans (idx 1 hn)))
  let T (w : N) (i : ℕ) := i ≤ n ∧ i ≠ 0 ∧ G.Adj (P.vertex i) w.val
  have lower (w : N) (i : ℕ) (h : T w i) : 4 ≤ i := by
    have ha := idx i h.1 ▸ h.2.2
    have := first_blocker (g:=6) hg hp (adj w w.property) (off w) (by rw [hlen]; exact h.1) h.2.1 ha.symm
    omega
  constructor
  refine ⟨T,?_,fun h=>h.2.2,fun hi hpos=>⟨fun h=>h.2.2, fun ha=>⟨hi,hpos,ha⟩⟩,
    fun h=>lower _ _ h,fun h=>h.1,?_⟩
  · intro w
    by_contra! none
    apply sat w w.property
    refine ⟨adj w w.property,?_,fun i hi hpos h => none i ⟨hi,hpos,h.symm⟩⟩
    intro i hi he
    exact off w ((he.trans (idx _ hi).symm) ▸ p.getVert_mem_support i)
  · intro w z i j hi hj hij different
    by_cases e : w=z
    · subst z
      have ne : i ≠ j := different.resolve_left (by simp)
      by_contra! hh
      have edge := (P.edges hi.1 hj.1).2 (Or.inl (by omega))
      exact no_short_triangle hg edge hi.2.2 hj.2.2
    · have ha := idx i hi.1 ▸ hi.2.2
      have hb := idx j hj.1 ▸ hj.2.2
      have := separated_blockers (g:=6) hg hp (adj w w.property) (adj z z.property)
        (off w) (off z) (fun h => e (Subtype.ext h)) (by have := lower _ _ hi; omega)
        hij (by rw [hlen]; exact hj.1) ha.symm hb.symm (by decide)
      omega


private theorem Contacts.slots {P : Chain G n} {N : Finset V} (C : Contacts P N)
    {m : ℕ} (f : ℕ → ℕ)
    (bd : ∀ w i, C.touches w i → f i < m)
    (close : ∀ w z i j,C.touches w i → C.touches z j → f i=f j → i ≤ j+1 ∧ j ≤ i+1) :
    N.card ≤ m ∧ (m ≤ N.card → ∀ k : Fin m, ∃ w i,C.touches w i ∧ f i=k.val ∧
      ∀ j, C.touches w j → j=i) := by
  classical
  have unique {w z i j} (h : C.touches w i) (h' : C.touches z j) (eq : f i=f j) : w=z ∧ i=j := by
    have ⟨a,b⟩ := close _ _ _ _ h h' eq
    by_contra! hne
    rcases le_total i j with le|le
    · have := C.separate h h' le (by by_cases e : w=z; exact Or.inr (hne e); exact Or.inl e)
      omega
    · have := C.separate h' h le (by by_cases e : w=z; exact Or.inr (Ne.symm (hne e)); exact Or.inl (Ne.symm e))
      omega
  choose idx hi using C.exists_site
  let F (w : N) : Fin m := ⟨f (idx w),bd _ _ (hi w)⟩
  have inj : Function.Injective F := fun w z e => (unique (hi w) (hi z) (congrArg Fin.val e)).1
  have count : N.card ≤ m := by simpa using Fintype.card_le_of_injective F inj
  refine ⟨count,fun enough k => ?_⟩
  have onto : Function.Surjective F := by
    apply ((Fintype.bijective_iff_injective_and_card F).2 ⟨inj,?_⟩).2
    simpa using count.antisymm enough
  obtain ⟨w,hw⟩ := onto k
  refine ⟨w,idx w,hi w,congrArg Fin.val hw,fun j hj => ?_⟩
  obtain ⟨z,hz⟩ := onto ⟨f j,bd _ _ hj⟩
  obtain ⟨eq,e⟩ := unique (hi z) hj (congrArg Fin.val hz)
  exact eq ▸ e.symm

private theorem Contacts.interval {P : Chain G n} {N : Finset V} (C : Contacts P N)
    {M : ℕ} (bd : ∀ w i,C.touches w i → i ≤ M) : N.card ≤ (M-2)/2 := by
  apply (C.slots (fun i => (i-4)/2) ?_ ?_).1
  · intro w i h; have := bd _ _ h; have := C.lower h; omega
  · intro w z i j h h' e; have := C.lower h; have := C.lower h'; omega

private theorem near_contact (hc : G.Connected) {P : Chain G n} {w : V} {i : ℕ}
    (ha : G.Adj (P.vertex 0) w) (hb : G.Adj (P.vertex i) w) :
    G.dist (P.vertex 0) (P.vertex i) ≤ 2 := by
  have tr := hc.dist_triangle (u:=P.vertex 0) (v:=w) (w:=P.vertex i)
  rwa [dist_eq_one_iff_adj.mpr ha,dist_eq_one_iff_adj.mpr hb.symm] at tr

private theorem almost_geodesic (hc : G.Connected) {a v : V} (q : G.Walk a v)
    {e : ℕ} (he : q.length ≤ G.dist a v+e) {j : ℕ} (hj : j ≤ q.length) :
    j ≤ G.dist a (q.getVert j)+e ∧
    G.dist (q.getVert j) v ≤ q.length-j ∧ q.length-j ≤ G.dist (q.getVert j) v+e := by
  have ht := G.dist_le (q.take j)
  have hd := G.dist_le (q.drop j)
  simp only [Walk.take_length,Nat.min_eq_left hj,Walk.drop_length] at ht hd
  have := hc.dist_triangle (u:=a) (v:=q.getVert j) (w:=v)
  omega

private theorem suffix_limit (hc : G.Connected) (P : Chain G n) {a v : V} (q : G.Walk a v)
    {e : ℕ} (hq : q.length ≤ G.dist a v+e) {t r skip : ℕ} (hlen : n=t+q.length)
    (suf : ∀ j, skip ≤ j → j ≤ q.length → P.vertex (t+j)=q.getVert j)
    (hskip : skip ≤ r+2+e) (hnear : G.dist a (P.vertex 0) ≤ r) {i : ℕ}
    (hi : i ≤ n) (hblock : G.dist (P.vertex 0) (P.vertex i) ≤ 2) : i ≤ t+r+2+e := by
  by_cases h : t+skip ≤ i
  · have e := suf (i-t) (by omega) (by omega)
    rw [Nat.add_sub_of_le (show t ≤ i by omega)] at e
    have he := (almost_geodesic hc q hq (j:=i-t) (by omega)).1
    rw [←e] at he
    have := hc.dist_triangle (u:=a) (v:=P.vertex 0) (w:=P.vertex i)
    omega
  · omega

private def slot (t b i : ℕ) : ℕ := if i<t then (i-4)/2 else (t-3)/2+(i-b)/2

private theorem geodesic_slots (hc : G.Connected) (P : Chain G n) {t : ℕ}
    (e : ℕ) (he : e ≤ 1) (hm : ∀ i, t ≤ i → i ≤ n →
      G.dist (P.vertex i) (P.vertex n) ≤ n-i ∧ n-i ≤ G.dist (P.vertex i) (P.vertex n)+e)
    {N : Finset V} (C : Contacts P N)
    (ha : ∀ w∈N,G.Adj (P.vertex 0) w) :
    ∃ b, (∀ w i, C.touches w i → t ≤ i → b ≤ i ∧ i ≤ b+4+e) ∧
    N.card ≤ (t-3)/2+3 ∧ ((t-3)/2+3 ≤ N.card → ∀ k : Fin ((t-3)/2+3),
      ∃ w i,C.touches w i ∧ slot t b i=k.val ∧ ∀ j,C.touches w j → j=i) := by
  let b := n-(G.dist (P.vertex 0) (P.vertex n)+2+e)
  have win (w i) (h : C.touches w i) (ht : t ≤ i) : b ≤ i ∧ i ≤ b+4+e := by
    have hd := near_contact hc (ha w w.property) (C.adjacent h)
    have h₁ := hc.dist_triangle (u:=P.vertex 0) (v:=P.vertex i) (w:=P.vertex n)
    have h₂ := hc.dist_triangle (u:=P.vertex i) (v:=P.vertex 0) (w:=P.vertex n)
    rw [G.dist_comm (u:=P.vertex i) (v:=P.vertex 0)] at h₂
    have ⟨hh,hh'⟩ := hm i ht (C.upper h)
    have := C.upper h
    dsimp [b]; omega
  refine ⟨b,win,C.slots (slot t b) ?_ ?_⟩
  · intro w i h
    dsimp [slot]; split_ifs
    · have := C.lower h; omega
    · have := win w i h (by omega); omega
  · intro w z i j h h' e
    dsimp [slot] at e
    have := C.lower h; have := C.lower h'
    split_ifs at e <;> first | omega | (have := win w i h (by omega); have := win z j h' (by omega); omega)


private theorem seeded_tail [Fintype V] [DecidableEq V] (hg : 6 ≤ G.egirth) (hc : G.Connected)
    (S : Finset V) (a x : S) {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1)
    (hq : q.length ≤ G.dist a.val v+e) (hq' : Chordless q)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1) :
    ∃ t n, ∃ P : Chain G n, n=t+q.length ∧ P.vertex (t-1)=x.val ∧
      (∀ j ≤ q.length,P.vertex (t+j)=q.getVert j) ∧ (∀ i ≤ t,P.vertex i∈S) ∧
      (∀ z∈S,¬Good P z) := by
  have off := hq'.pending_off_path hax hx
  let seed := q.cons hax.symm
  have hs : Chordless seed := hq'.extend hax off (by
    intro i hi hpos ha
    have := first_blocker (g:=6) hg hq' hax off hi hpos ha
    have hh := (almost_geodesic hc q hq hi).1
    have ht := hc.dist_triangle (u:=a.val) (v:=x.val) (w:=q.getVert i)
    rw [dist_eq_one_iff_adj.mpr hax,dist_eq_one_iff_adj.mpr ha] at ht
    omega)
  obtain ⟨u,p,s,hu,hp,hlen,hsuf,hpre,sat⟩ := exists_saturated_inside (S : Set V) seed hs x.property
  let P := chainOfChordless p hp
  have vtx (i) : P.vertex i=p.getVert i := rfl
  have hl : p.length=s+1+q.length := by change p.length=s+(q.length+1) at hlen; omega
  have suf (j) : P.vertex (s+1+j)=q.getVert j := by
    rw [vtx,show s+1+j=s+(j+1) by omega,hsuf]
    rfl
  have root : P.vertex s=x.val := by simpa [vtx,seed] using hsuf 0
  have anchor : P.vertex (s+1)=a.val := by simpa using suf 0
  refine ⟨s+1,p.length,P,hl,by simpa using root,fun j _ => suf j,?_,?_⟩
  · intro i hi
    by_cases h : i<s
    · exact hpre i h
    rcases (show i=s ∨ i=s+1 by omega) with rfl|rfl
    · exact root ▸ x.property
    · exact anchor ▸ a.property
  · intro z hz good
    have ha : G.Adj u z := by simpa [vtx] using good.1
    have hoff : z ∉ p.support := by
      intro h
      obtain ⟨i,eq,hi⟩ := Walk.mem_support_iff_exists_getVert.mp h
      exact good.2.1 i hi eq.symm
    obtain ⟨i,hi,hn,ha'⟩ := sat z hz ha hoff
    exact good.2.2 i hi hn ha'


private theorem tight_rotation (hc : G.Connected)
    (P : Chain G n) {a v : V} (q : G.Walk a v) {e t d : ℕ}
    (he : e ≤ 1) (hq : q.length ≤ G.dist a v+e) (hn : n=t+q.length)
    (suf : ∀ j ≤ q.length,P.vertex (t+j)=q.getVert j)
    (hd : 4 ≤ d) (ht : t=2*d-5 ∨ t=2*d-4)
    {N : Finset V} (C : Contacts P N) (degree : d-1 ≤ N.card)
    (ha : ∀ w∈N,G.Adj (P.vertex 0) w) :
    ∃ j, ∃ R : Chain G n, 1 ≤ j ∧ j ≤ 2+e ∧ R.vertex 0=P.vertex (t+j-2) ∧
      (∀ k, j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k) ∧
      ∃ w∈N,G.Adj (P.vertex 0) w ∧ G.Adj (P.vertex (t+j)) w ∧ R.vertex (t+j-1)=w ∧ (t=2*d-5 → j ≤ 2) := by
  have anchor : P.vertex t=a := by simpa using suf 0 (Nat.zero_le _)
  have last : P.vertex n=v := hn ▸ (suf _ le_rfl).trans q.getVert_length
  have metric (i) (hi : t ≤ i) (hin : i ≤ n) :
      G.dist (P.vertex i) (P.vertex n) ≤ n-i ∧ n-i ≤ G.dist (P.vertex i) (P.vertex n)+e := by
    have eq := suf (i-t) (by omega)
    rw [Nat.add_sub_of_le hi] at eq
    have ⟨_,a₁,a₂⟩ := almost_geodesic hc q hq (j:=i-t) (by omega)
    rw [eq,last]
    omega
  obtain ⟨b,win,count,full⟩ := geodesic_slots hc P e he metric C ha
  let h := (t-3)/2
  have fill : h+3 ≤ N.card := by dsimp [h]; omega
  let r := if t=2*d-5 then 3 else 4
  have rbd : r=3 ∧ t=2*d-5 ∨ r=4 ∧ t=2*d-4 := by
    dsimp [r]; split_ifs <;> omega
  have near : G.dist a (P.vertex 0) ≤ r := by
    by_cases short : t ≤ r
    · have dist := P.dist_le_sub hc (i:=0) (j:=t) (Nat.zero_le _) (by omega)
      rw [anchor,Nat.sub_zero,G.dist_comm] at dist
      omega
    have hpos : 0 < h := by dsimp [h]; omega
    obtain ⟨w,i,hwi,hcode,_⟩ := full fill ⟨h-1,by omega⟩
    change slot t b i=h-1 at hcode
    have ilow := C.lower hwi
    dsimp [slot] at hcode
    split_ifs at hcode with hi
    · have dist := P.dist_le_sub hc (i:=i) (j:=t) (by omega) (by omega)
      rw [anchor,G.dist_comm] at dist
      have near' := near_contact hc (ha w w.property) (C.adjacent hwi)
      have tri := hc.dist_triangle (u:=a) (v:=P.vertex i) (w:=P.vertex 0)
      rw [G.dist_comm (u:=P.vertex i) (v:=P.vertex 0)] at tri
      dsimp [h] at hcode
      omega
    · dsimp [h] at hcode; omega
  let Witness (i : ℕ) := ∃ w : N,C.touches w i ∧ ∀ j,C.touches w j → j=i
  have get (z : Fin 3) : ∃ i, t ≤ i ∧ i ≤ t+r+2+e ∧ b ≤ i ∧ i ≤ b+4+e ∧
      (i-b)/2=z.val ∧ Witness i := by
    obtain ⟨w,i,hw,hcode,priv⟩ := full fill ⟨h+z.val,by have := z.isLt; omega⟩
    change slot t b i=h+z.val at hcode
    have ilow := C.lower hw
    dsimp [slot] at hcode
    split_ifs at hcode with small
    · dsimp [h] at hcode; omega
    · have hi : t ≤ i := by omega
      have ⟨lo,up⟩ := win w i hw hi
      have lim := suffix_limit hc P q hq hn (skip:=0) (fun j _ hj => suf j hj)
        (Nat.zero_le _) near (C.upper hw) (near_contact hc (ha w w.property) (C.adjacent hw))
      refine ⟨i,hi,lim,lo,up,?_,w,hw,priv⟩
      dsimp [h] at hcode; omega
  obtain ⟨i₀,ht₀,hl₀,hb₀,hu₀,hs₀,hw₀⟩ := get 0
  obtain ⟨i₁,ht₁,hl₁,hb₁,hu₁,hs₁,hw₁⟩ := get 1
  obtain ⟨i₂,ht₂,hl₂,hb₂,hu₂,hs₂,hw₂⟩ := get 2
  change (i₀-b)/2=0 at hs₀
  change (i₁-b)/2=1 at hs₁
  change (i₂-b)/2=2 at hs₂
  have sep {i j} (hi : Witness i) (hj : Witness j) (hne : i<j) : i+2 ≤ j := by
    obtain ⟨w,hw,-⟩ := hi
    obtain ⟨z,hz,-⟩ := hj
    exact C.separate hw hz hne.le (Or.inr hne.ne)
  have sep₁ := sep hw₀ hw₁ (by omega)
  have sep₂ := sep hw₁ hw₂ (by omega)
  have noT (odd : t=2*d-5) (touch : Witness t) : False := by
    obtain ⟨z,hz,-⟩ := touch
    have tl := C.lower hz
    have hpos : 0 < h := by dsimp [h]; omega
    obtain ⟨w,i,hwi,hcode,-⟩ := full fill ⟨h-1,by omega⟩
    change slot t b i=h-1 at hcode
    have ilow := C.lower hwi
    dsimp [slot] at hcode
    split_ifs at hcode with hi
    · have ieq : i=t-1 := by dsimp [h] at hcode; omega
      have := C.separate hwi hz hi.le (Or.inr hi.ne)
      omega
    · dsimp [h] at hcode; omega
  let allowance := if t=2*d-5 then 0 else e
  have which : ∃ i, t+1 ≤ i ∧ i ≤ t+2+allowance ∧ Witness i := by
    have fst (odd : t=2*d-5) : i₀ ≠ t := fun eq => noT odd (eq ▸ hw₀)
    have : (t+1 ≤ i₀ ∧ i₀ ≤ t+2+allowance) ∨ (t+1 ≤ i₁ ∧ i₁ ≤ t+2+allowance) ∨
        (t+1 ≤ i₂ ∧ i₂ ≤ t+2+allowance) := by
      dsimp [allowance]; split_ifs with odd
      · have := fst odd; omega
      · omega
    rcases this with h|h|h
    · exact ⟨i₀,h.1,h.2,hw₀⟩
    · exact ⟨i₁,h.1,h.2,hw₁⟩
    · exact ⟨i₂,h.1,h.2,hw₂⟩
  obtain ⟨i,lo,up,w,hw,hpriv⟩ := which
  have ae : allowance ≤ e := by dsimp [allowance]; split_ifs <;> omega
  let R := P.rotateAt i (C.lower hw) (C.upper hw) (ha w w.property) (C.adjacent hw)
    (fun j hj hp hjw => hpriv j ((C.iff_adj hj hp).2 hjw))
  refine ⟨i-t,R,by omega,by omega,?_,?_,?_⟩
  · have ilow := C.lower hw
    simp [R,Chain.rotateAt,show ¬i ≤ 0 by omega,show 1≠i by omega,Nat.add_sub_of_le (show t ≤ i by omega)]
  · intro k hk hlen
    simpa [R,Chain.rotateAt,show i ≤ t+k by omega] using suf k hlen
  · refine ⟨w,w.property,ha w w.property,?_,?_,?_⟩
    · rw [Nat.add_sub_of_le (show t ≤ i by omega)]; exact C.adjacent hw
    · have ilow := C.lower hw
      simp [R,Chain.rotateAt,Nat.add_sub_of_le (show t ≤ i by omega),show ¬i ≤ i-1 by omega,show i-1+1=i by omega]
    · intro odd; simp [allowance,odd] at up; omega


variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem girth_six_core_rotations (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a x : S) {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1)
    (hq : q.length ≤ G.dist a.val v+e) (hpath : Chordless q) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1) :
    ∃ t n, ∃ P : Chain G n, n=t+q.length ∧ P.vertex (t-1)=x.val ∧
      (∀ j ≤ q.length,P.vertex (t+j)=q.getVert j) ∧
      ∃ inside : ∀ i ≤ t,P.vertex i∈S, ∀ D, d ≤ D →
      D ≤ (G.induce (S : Set V)).degree ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩ →
      2*D-5 ≤ t ∧ (t=2*D-5 ∨ t=2*D-4 → ∃ j, ∃ R : Chain G n, 1 ≤ j ∧ j ≤ 2+e ∧
        R.vertex 0=P.vertex (t+j-2) ∧ (∀ k,j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k) ∧
        ∃ w∈S,G.Adj (P.vertex 0) w ∧ G.Adj (P.vertex (t+j)) w ∧ R.vertex (t+j-1)=w ∧ (t=2*D-5 → j ≤ 2)) := by
  classical
  obtain ⟨t,n,P,hn,px,suf,inside,sat⟩ := seeded_tail hg hc S a x q he hq hpath hax hx
  let u : S := ⟨P.vertex 0,inside 0 (Nat.zero_le _)⟩
  let A := coreNeighbors (G:=G) S u
  let N := A.erase (P.vertex 1)
  have nc : A.card=(G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have er : A.card-1 ≤ N.card := Finset.pred_card_le_card_erase
  have low : d-1 ≤ N.card := by have := hmin u; omega
  have mem (w) (hw : w∈N) := mem_coreNeighbors (Finset.mem_erase.mp hw).2
  let C := contacts_of_stall P (by omega) hg N (fun w hw => (mem w hw).1)
    (fun w hw => (Finset.mem_erase.mp hw).1) (fun w hw => sat _ (mem w hw).2)
  have deg := geodesic_slots hc P e he (t:=t) (fun i hi hin => by
    have eq := suf (i-t) (by omega)
    rw [Nat.add_sub_of_le hi] at eq
    have ⟨_,a₁,a₂⟩ := almost_geodesic hc q hq (j:=i-t) (by omega)
    have last : P.vertex n=v := hn ▸ (suf _ le_rfl).trans q.getVert_length
    rw [eq,last]; omega) C (fun w hw => (mem w hw).1)
  obtain ⟨_,_,upper,_⟩ := deg
  have three : 3 ≤ t := by
    by_contra! small
    have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
    have near := P.dist_le_sub hc (i:=0) (j:=t) (by omega) (by omega)
    rw [anchor,Nat.sub_zero,G.dist_comm] at near
    have bd := C.interval (M:=2*t+2+e) (fun w i h => by
      have := suffix_limit hc P q hq hn (skip:=0) (fun j _ hj => suf j hj)
        (Nat.zero_le _) near (C.upper h) (near_contact hc (mem w w.property).1 (C.adjacent h))
      omega)
    omega
  refine ⟨t,n,P,hn,px,suf,inside,fun D hD hDu => ?_⟩
  change D ≤ (G.induce (S : Set V)).degree u at hDu
  have degD : D-1 ≤ N.card := by omega
  refine ⟨by omega, fun ht => ?_⟩
  obtain ⟨j,R,hj,hi,r0,rs,w,hw,huw,hwi⟩ := tight_rotation hc P q he hq hn suf
    (hd.trans hD) ht C degD (fun w hw => (mem w hw).1)
  exact ⟨j,R,hj,hi,r0,rs,w,(mem w hw).2,huw,hwi⟩

private theorem core_rotations (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a x : S) {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1)
    (hq : q.length ≤ G.dist a.val v+e) (hpath : Chordless q) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1) :
    ∃ t n, ∃ P : Chain G n, n=t+q.length ∧ P.vertex (t-1)=x.val ∧
      (∀ j ≤ q.length,P.vertex (t+j)=q.getVert j) ∧ 2*d-5 ≤ t ∧
      (t=2*d-5 ∨ t=2*d-4 → ∃ j, ∃ R : Chain G n, 1 ≤ j ∧ j ≤ 2+e ∧
        R.vertex 0=P.vertex (t+j-2) ∧ ∀ k,j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k) := by
  obtain ⟨t,n,P,hn,px,suf,inside,all⟩ :=
    girth_six_core_rotations hc hg S hd hmin a x q he hq hpath hl hax hx
  obtain ⟨lower,rotate⟩ := all d le_rfl (hmin _)
  refine ⟨t,n,P,hn,px,suf,lower,fun ht => ?_⟩
  obtain ⟨j,R,hj,hi,r0,rs,_⟩ := rotate ht
  exact ⟨j,R,hj,hi,r0,rs⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem girth_six_grow_among (hg : 6 ≤ G.egirth) (hc : G.Connected) (R : Chain G n)
    {a v : V} (q : G.Walk a v) {e t j r : ℕ} (hq : q.length ≤ G.dist a v+e)
    (hlen : n=t+q.length) (hn : 2 ≤ n) (hj : j ≤ r+2+e)
    (suf : ∀ k,j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k)
    (near : G.dist a (R.vertex 0) ≤ r) (A : Finset V)
    (adj : ∀ w∈A,G.Adj (R.vertex 0) w) (size : (t+r+2+e)/2 < A.card) :
    ∃ w∈A, Good R w := by
  classical
  by_contra! none
  let B := A.erase (R.vertex 1)
  let C := contacts_of_stall R (by omega) hg B (fun w hw => adj _ (Finset.mem_erase.mp hw).2)
    (fun w hw => (Finset.mem_erase.mp hw).1) (fun w hw => none _ (Finset.mem_erase.mp hw).2)
  have er : A.card-1 ≤ B.card := Finset.pred_card_le_card_erase
  have ub := C.interval (M:=t+r+2+e) (fun w i h =>
    suffix_limit hc R q hq hlen suf hj near (C.upper h)
      (near_contact hc (adj _ (Finset.mem_erase.mp w.property).2) (C.adjacent h)))
  omega

theorem girth_six_core_growth (hg : 6 ≤ G.egirth) (hc : G.Connected) (R : Chain G n)
    (S : Finset V) (y : S) (hy : R.vertex 0=y.val) {a v : V} (q : G.Walk a v)
    {e t j r : ℕ} (hq : q.length ≤ G.dist a v+e)
    (hlen : n=t+q.length) (hn : 2 ≤ n) (hj : j ≤ r+2+e)
    (suf : ∀ k,j ≤ k → k ≤ q.length → R.vertex (t+k)=q.getVert k)
    (near : G.dist a y.val ≤ r) (size : (t+r+2+e)/2 < (G.induce (S : Set V)).degree y) :
    n+2 ≤ G.path := by
  obtain ⟨w,_,hw⟩ := girth_six_grow_among hg hc R q hq hlen hn hj suf (hy ▸ near) (coreNeighbors (G:=G) S y)
    (fun z hz => hy ▸ (mem_coreNeighbors hz).1) (by rwa [coreNeighbors_card])
  exact (grow R w hw).length_le


/-- A shortest path, or a chordless path one edge longer than the distance
whose first two vertices are in the core, gains at least 2d−3 vertices. -/
theorem girth_six_pointed_core (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a : S) {v : V} (q : G.Walk a.val v) {e : ℕ} (he : e ≤ 1)
    (hq : q.length ≤ G.dist a.val v+e) (hp : Chordless q) (hl : 5 ≤ q.length)
    (hcore : e=1 → q.getVert 1∈S) : q.length+2*d-3 ≤ G.path := by
  classical
  let H := G.induce (S : Set V)
  have pick : ∃ x∈H.neighborFinset a,(x : S).val ≠ q.getVert 1 := by
    by_contra! none
    have card : (H.neighborFinset a).card ≤ 1 := Finset.card_le_one.mpr
      (fun x hx y hy => Subtype.ext ((none x hx).trans (none y hy).symm))
    rw [H.card_neighborFinset_eq_degree] at card
    have deg : d ≤ H.degree a := hmin a
    omega
  obtain ⟨x,hx,hx'⟩ := pick
  have hax : G.Adj a.val x.val := (H.mem_neighborFinset _ _).mp hx
  obtain ⟨t,n,P,hn,px,suf,lower,rot⟩ := core_rotations hc hg S hd hmin a x q he hq hp hl hax hx'
  have plen := P.length_le
  by_contra! short
  have ht : t=2*d-5 := by omega
  obtain ⟨j,R,hj,up,root,rs⟩ := rot (Or.inl ht)
  have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
  have info : ∃ y : S,R.vertex 0=y.val ∧ G.dist a.val y.val ≤ 1 := by
    rcases (show j=1 ∨ j=2 ∨ j=3 ∧ e=1 by omega) with rfl|rfl|⟨rfl,he'⟩
    · exact ⟨x,root.trans ((show t+1-2=t-1 by omega) ▸ px),(dist_eq_one_iff_adj.mpr hax).le⟩
    · exact ⟨a,root.trans (by simpa using anchor),by simp⟩
    · refine ⟨⟨q.getVert 1,hcore he'⟩,root.trans ?_,?_⟩
      · simpa [show t+3-2=t+1 by omega] using suf 1 (by omega)
      · have edge := q.adj_getVert_succ (i:=0) (by omega)
        rw [q.getVert_zero] at edge
        exact (dist_eq_one_iff_adj.mpr edge).le
  obtain ⟨y,hy,near⟩ := info
  have := girth_six_core_growth hg hc R S y hy q hq hn (by omega) (by omega) rs near (by
    have := hmin y; omega)
  omega

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem genuine_chordless {a v : V} (q : G.Walk a v) (hq : q.length=G.dist a v) :
    Chordless q := ⟨q.isPath_of_length_eq_dist hq,
      fun _ _ hi hj => (adj_getVert_iff_consecutive_of_length_eq_dist q hq hi hj).1⟩

/-- An edge of the core within one distance layer produces one extra vertex
beyond the pointed geodesic bound. -/
theorem girth_six_equal_layer_gain (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a y : S) {v : V} (hay : G.Adj a.val y.val) (eq : G.dist a.val v=G.dist y.val v)
    (large : 5 ≤ G.dist a.val v) : G.dist a.val v+2*d-2 ≤ G.path := by
  obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist y.val v
  have hp := genuine_chordless q hq
  have suffix (i) (hi : i ≤ q.length) : G.dist (q.getVert i) v=q.length-i := by
    simpa using dist_getVert_eq_sub_of_le_of_length_eq_dist q hq hi le_rfl
  have hne : a.val ≠ q.getVert 1 := by
    intro h
    have := suffix 1 (by omega)
    rw [←h] at this
    omega
  have off := hp.pending_off_path hay.symm hne
  have hQ : Chordless (q.cons hay) := hp.extend hay.symm off (by
    intro i hi pos edge
    have := first_blocker (g:=6) hg hp hay.symm off hi pos edge
    have tr := hc.dist_triangle (u:=a.val) (v:=q.getVert i) (w:=v)
    rw [dist_eq_one_iff_adj.mpr edge,suffix i hi] at tr
    omega)
  have hlen : (q.cons hay).length=q.length+1 := rfl
  have h := girth_six_pointed_core hc hg S hd hmin a (q.cons hay) (e:=1) le_rfl
    (by omega) hQ (by omega) (fun _ => by simp)
  omega


/-- A prescribed first core neighbor of the geodesic anchor has few
high-degree neighbors whenever the sharp even bound fails. -/
theorem girth_six_geodesic_high_neighbors (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) {d : ℕ} (hd : 4 ≤ d) (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z)
    (a x : S) {v : V} (q : G.Walk a.val v) (hq : q.length=G.dist a.val v) (hl : 5 ≤ q.length)
    (hax : G.Adj a.val x.val) (hx : x.val ≠ q.getVert 1) (short : G.path ≤ q.length+2*d-3)
    (A : Finset S) (hA : ∀ z∈A,(G.induce (S : Set V)).Adj x z ∧
      (z=a ∨ d < (G.induce (S : Set V)).degree z)) : A.card ≤ d-1 := by
  classical
  by_contra! card
  have metric : q.length ≤ G.dist a.val v+0 := hq.le
  obtain ⟨t,n,P,hn,px,suf,lower,rot⟩ :=
    core_rotations hc hg S hd hmin a x q (e:=0) (by decide) metric (genuine_chordless q hq) hl hax hx
  have plen := P.length_le
  have ht : t=2*d-5 ∨ t=2*d-4 := by clear * - hd lower hn plen short; omega
  obtain ⟨j,R,lo,up,root,rs⟩ := rot ht
  clear rot
  have anchor : P.vertex t=a.val := by simpa using suf 0 (Nat.zero_le _)
  have rX (h : j=1) : R.vertex 0=x.val := by rwa [h,show t+1-2=t-1 by omega,px] at root
  have rA (h : j=2) : R.vertex 0=a.val := by rwa [h,show t+2-2=t by omega,anchor] at root
  have nearX : G.dist a.val x.val ≤ 1 := (dist_eq_one_iff_adj.mpr hax).le
  have two {u : S} (hu : R.vertex 0=u.val) {r : ℕ} (near : G.dist a.val u.val ≤ r)
      (hj : j ≤ r+2) {B : Finset S} (adj : ∀ z∈B,(G.induce (S : Set V)).Adj u z)
      (size : (t+r+2)/2 < B.card)
      (next : ∀ z∈B,(t+1+(r+1)+2)/2 < (G.induce (S : Set V)).degree z ∨ z=a ∧ j=1) :
      n+3 ≤ G.path := by
    let F := B.map (Function.Embedding.subtype (·∈S))
    have neigh (w) (hw : w∈F) : G.Adj (R.vertex 0) w := by
      obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hw
      exact hu ▸ adj z hz
    obtain ⟨z,hz,g⟩ := girth_six_grow_among hg hc R q metric hn (by omega) (by omega) rs (hu ▸ near) F neigh
      (by simpa [F] using size)
    obtain ⟨y,hy,eq⟩ := Finset.mem_map.mp hz
    have yroot : (grow R z g).vertex 0=y.val := eq.symm
    have ysuf (k) (hk : j ≤ k) (hL : k ≤ q.length) :
        (grow R z g).vertex (t+1+k)=q.getVert k := by
      rw [show t+1+k=(t+k)+1 by omega]
      exact rs k hk hL
    have dY : (t+1+(r+1)+2)/2 < (G.induce (S : Set V)).degree y := by
      rcases next y hy with h|⟨hya,hj₁⟩
      · exact h
      have edge : G.Adj ((grow R z g).vertex 0) ((grow R z g).vertex (t+1+1)) := by
        rw [yroot,hya,ysuf 1 hj₁.le (by omega)]
        simpa using q.adj_getVert_succ (i:=0) (by omega)
      have := ((grow R z g).edges (Nat.zero_le _) (by omega)).1 edge
      omega
    have ynear : G.dist a.val y.val ≤ r+1 := by
      have ay : G.Adj u.val y.val := adj y hy
      have tri := hc.dist_triangle (u:=a.val) (v:=u.val) (w:=y.val)
      rw [dist_eq_one_iff_adj.mpr ay] at tri
      omega
    exact girth_six_core_growth hg hc (grow R z g) S y yroot q metric (by omega) (by omega) (by omega)
      ysuf ynear dY
  rcases ht with ht|ht
  · rcases (show j=1 ∨ j=2 by omega) with j₁|j₂
    · have := two (rX j₁) nearX (by omega) (B:=A) (fun z hz => (hA z hz).1) (by omega)
        (fun z hz => ((hA z hz).2).elim (fun h => Or.inr ⟨h,j₁⟩) (fun h => Or.inl (by omega)))
      omega
    · let H := G.induce (S : Set V)
      have := two (rA j₂) (r:=0) (by simp) (by omega) (B:=H.neighborFinset a)
        (fun z hz => (H.mem_neighborFinset _ _).mp hz)
        (by rw [H.card_neighborFinset_eq_degree]; have h : d ≤ H.degree a := hmin a; omega)
        (fun z _ => Or.inl (by have := hmin z; omega))
      omega
  · have info : ∃ y : S,R.vertex 0=y.val ∧ G.dist a.val y.val ≤ 1 := by
      rcases (show j=1 ∨ j=2 by omega) with j₁|j₂
      · exact ⟨x,rX j₁,nearX⟩
      · exact ⟨a,rA j₂,by simp⟩
    obtain ⟨y,hy,near⟩ := info
    have := girth_six_core_growth hg hc R S y hy q metric hn (by omega) (by omega) rs near (by
      have := hmin y; omega)
    omega

/-- A dense core gives the even threshold plus any distance attainable
from every core vertex, measured in the whole graph. This gains an extra
vertex when the core avoids all centers. -/
theorem girth_six_even_core_distance (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) (hS : S.Nonempty) {m r : ℕ} (hm : 3 ≤ m) (hr : 5 ≤ r)
    (hmin : ∀ z : S,m < (G.induce (S : Set V)).degree z)
    (dense : S.card*(2*m) ≤ ∑ z : S,(G.induce (S : Set V)).degree z)
    (far : ∀ a : S,∃ v,r ≤ G.dist a.val v) : r+2*m ≤ G.path := by
  classical
  by_contra! hshort
  let H := G.induce (S : Set V)
  let d := m+1
  have central (a : S) (v : V) : G.dist a.val v ≤ r := by
    by_cases h : 5 ≤ G.dist a.val v
    · obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
      have := girth_six_pointed_core hc hg S (by omega : 4 ≤ m+1) hmin a q (e:=0)
        (by decide) hq.le (genuine_chordless q hq) (by omega) (by simp)
      omega
    · omega
  have test (a x : S) (hax : H.Adj a x) (A : Finset S)
      (hA : ∀ z∈A, H.Adj x z ∧ (z=a ∨ d<H.degree z)) : A.card ≤ d-1 := by
    obtain ⟨v,hv⟩ := far a
    obtain ⟨q,_,hq⟩ := hc.exists_path_of_dist a.val v
    have hcen := central a v
    have other : ∃ y ∈ H.neighborFinset a, y ≠ x := by
      by_contra! hall
      have h1 : (H.neighborFinset a).card ≤ 1 :=
        Finset.card_le_one.mpr (fun u hu w hw => (hall u hu).trans (hall w hw).symm)
      rw [H.card_neighborFinset_eq_degree] at h1
      have hh := hmin a
      change _ < H.degree a at hh
      omega
    obtain ⟨y,hy,hyx⟩ := other
    have hay : G.Adj a.val y.val := (H.mem_neighborFinset _ _).mp hy
    have hcy := central y v
    have hne : G.dist a.val v ≠ G.dist y.val v := by
      intro equal
      have := girth_six_equal_layer_gain hc hg S (by omega : 4 ≤ m+1) hmin a y hay equal (by omega)
      omega
    have htri := hc.dist_triangle (u := a.val) (v := y.val) (w := v)
    rw [dist_eq_one_iff_adj.mpr hay] at htri
    obtain ⟨w,_,hw⟩ := hc.exists_path_of_dist y.val v
    let p := w.cons hay
    have hp : p.length=G.dist a.val v := by change w.length+1=_; omega
    have hx : x.val ≠ p.getVert 1 := by
      have e : p.getVert 1=y.val := by simp [p]
      exact fun h => hyx (Subtype.ext (h.trans e).symm)
    exact girth_six_geodesic_high_neighbors hc hg S (by omega : 4 ≤ m+1) hmin a x p hp
      (by omega) hax hx (by omega) A hA
  exact core_incidence_contradiction S hS hm hmin dense test

private theorem even_large [Nonempty V] (hc : G.Connected) (hg : 6 ≤ G.egirth) {m : ℕ} (hm : 3 ≤ m)
    (hav : (2*m)*Fintype.card V ≤ ∑ v, G.degree v) (hr : 5 ≤ G.radius.toNat) :
    G.radius.toNat + 2*m ≤ G.path := by
  classical
  have hh : 2*(∑ _v : V, m) ≤ ∑ v,G.degree v := by
    simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using hav
  obtain ⟨S,hS,hmin,hsum⟩ := exists_weighted_degree_core G (fun _ => m) (by omega) hh
  let H := G.induce (S : Set V)
  have dense : S.card*(2*m) ≤ ∑ u : S,H.degree u := by
    simpa [Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using hsum
  apply girth_six_even_core_distance hc hg S hS hm hr hmin dense
  intro a
  obtain ⟨v,q,hq,hv⟩ := exists_geodesic_ge_radius G hc a.val
  exact ⟨v,hq ▸ hv⟩

/-- At girth at least six the radius plus every even threshold for the
average degree is a lower bound on the longest induced path, at all radii. -/
theorem radius_add_even_density_le_path_girth_six [Nonempty V] (hc : G.Connected) (hg : 6 ≤ G.egirth)
    {m : ℕ} (hav : (2*m)*Fintype.card V ≤ ∑ v,G.degree v) :
    G.radius.toNat+2*m ≤ G.path := by
  by_cases hm : 2 ≤ m
  · have hp := girth_six_density_path_bound hg (by omega : 4 ≤ 2*m) hav
    by_cases hr : 5 ≤ G.radius.toNat
    · by_cases big : 3 ≤ m
      · exact even_large hc hg big hav hr
      have := chung_bound_nat G hc
      omega
    · omega
  by_cases hz : m=0
  · have := radius_add_one_le_path G hc
    omega
  obtain ⟨S,hS,hmin⟩ := exists_degree_core G (by omega : 0 < 2*m) hav
  let H := G.induce (S : Set V)
  obtain ⟨a,ha⟩ := hS
  have hg' : 6 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
  have hp := girth_six_min_degree_bound hg' (d:=2) le_rfl
    (fun z => by have h := hmin z; change _ ≤ H.degree z at h; omega) ⟨a,ha⟩
  have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
  have := chung_bound_nat G hc
  omega

/-- The exact floored conjecture for graphs of girth at least six with an
even floor, and an additive error of one vertex for an odd floor. -/
theorem radius_add_floor_le_path_girth_six_sharp [Nonempty V] (hc : G.Connected) (hg : 6 ≤ G.egirth) :
    G.radius.toNat+⌊l G⌋₊ ≤ G.path+(⌊l G⌋₊%2) := by
  have hd := sum_degree_ge_of_le_l (G:=G) (k:=⌊l G⌋₊)
    (Nat.floor_le (div_nonneg (Finset.sum_nonneg (fun v _ => Nat.cast_nonneg (G.indepNeighborsCard v)))
      (Nat.cast_nonneg _)))
  have hav := (Nat.mul_le_mul_right (Fintype.card V) (show 2*(⌊l G⌋₊/2) ≤ ⌊l G⌋₊ by omega)).trans hd
  have := radius_add_even_density_le_path_girth_six hc hg hav
  omega

/-- A core of minimum degree d gives radius plus 2d−3 at every radius.
In particular this is the full odd threshold 2m+1 when d≥m+2. -/
theorem girth_six_radius_core_sharp (hc : G.Connected) (hg : 6 ≤ G.egirth)
    (S : Finset V) (hS : S.Nonempty) {d : ℕ} (hd : 2 ≤ d)
    (hmin : ∀ z : S,d ≤ (G.induce (S : Set V)).degree z) :
    G.radius.toNat+2*d ≤ G.path+3 := by
  have : Nonempty V := hc.nonempty
  obtain ⟨a,ha⟩ := hS
  by_cases hr : 5 ≤ G.radius.toNat
  · by_cases hbig : 4 ≤ d
    · obtain ⟨v,q,hq,hrq⟩ := exists_geodesic_ge_radius G hc a
      have := girth_six_pointed_core hc hg S hbig hmin ⟨a,ha⟩ q (e:=0) (by decide) hq.le
        (genuine_chordless q hq) (by omega) (by simp)
      omega
    · have := chung_bound_nat G hc
      omega
  · let H := G.induce (S : Set V)
    have hg' : 6 ≤ H.egirth := hg.trans (IsContained.egirth_le ⟨Copy.induce G (S : Set V)⟩)
    have h := girth_six_min_degree_bound hg' hd hmin ⟨a,ha⟩
    have mono : H.path ≤ G.path := G.path_induce_le (S : Set V)
    omega


omit [Fintype V] in
/-- When all blocked neighbors fit into the positions through 2d+s, with
s at most one, every pair starting at an even k has a private contact.
If s=0 this contact is exactly at k. -/
theorem girth_six_interval_rotation (hg : 6 ≤ G.egirth) (hc : G.Connected) (P : Chain G n)
    (S : Finset V) (u : S) (hu : P.vertex 0=u.val) {a v : V} (q : G.Walk a v)
    {e t j r d s k : ℕ} (hq : q.length ≤ G.dist a v+e) (hn : n=t+q.length) (hL : 2 ≤ n)
    (hj : j ≤ r+2+e) (suf : ∀ i,j ≤ i → i ≤ q.length → P.vertex (t+i)=q.getVert i)
    (near : G.dist a u.val ≤ r) (size : d ≤ (G.induce (S : Set V)).degree u)
    (sat : ∀ z∈S,¬Good P z) (limit : t+r+2+e ≤ 2*d+s) (hs : s ≤ 1)
    (hk : 4 ≤ k) (keven : k%2=0) (kd : k ≤ 2*d) :
    ∃ i, ∃ R : Chain G n, k ≤ i ∧ i ≤ k+s ∧ R.vertex 0=P.vertex (i-2) ∧
      ∀ z,i ≤ z → R.vertex z=P.vertex z := by
  classical
  let A := coreNeighbors (G:=G) S u
  let N := A.erase (P.vertex 1)
  have nc : A.card=(G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have er : A.card-1 ≤ N.card := Finset.pred_card_le_card_erase
  have mem (z) (hz : z∈N) := mem_coreNeighbors (Finset.mem_erase.mp hz).2
  let C := contacts_of_stall P (by omega) hg N (fun z hz => hu ▸ (mem z hz).1)
    (fun z hz => (Finset.mem_erase.mp hz).1) (fun z hz => sat _ (mem z hz).2)
  have cap (w i) (h : C.touches w i) : i ≤ 2*d+s :=
    (suffix_limit hc P q hq hn suf hj (hu ▸ near) (C.upper h)
      (near_contact hc (hu ▸ (mem w w.property).1) (C.adjacent h))).trans limit
  let f (i : ℕ) := if i<k then (i-4)/2 else (k-4)/2+(i-k+1-s)/2
  have bound (w i) (h : C.touches w i) : f i < d-1 := by
    have := cap w i h; have := C.lower h
    dsimp [f]; split_ifs <;> omega
  have close (w z i j) (h : C.touches w i) (h' : C.touches z j) (eq : f i=f j) :
      i ≤ j+1 ∧ j ≤ i+1 := by
    have := C.lower h; have := C.lower h'
    dsimp [f] at eq; split_ifs at eq <;> omega
  obtain ⟨w,i,hwi,slot,priv⟩ := (C.slots f bound close).2 (by omega) ⟨(k-4)/2,by omega⟩
  change f i=(k-4)/2 at slot
  have ilo := C.lower hwi
  have bounds : k ≤ i ∧ i ≤ k+s := by dsimp [f] at slot; split_ifs at slot <;> omega
  let R := P.rotateAt i ilo (C.upper hwi) (hu ▸ (mem w w.property).1) (C.adjacent hwi)
    (fun j hj hpos hjw => priv j ((C.iff_adj hj hpos).2 hjw))
  refine ⟨i,R,bounds.1,bounds.2,?_,fun z hz => ?_⟩
  · simp [R,Chain.rotateAt,show ¬i ≤ 0 by omega,show 1≠i by omega]
  · simp [R,Chain.rotateAt,hz]


omit [Fintype V] in
/-- The usual geodesic contact count gives a single extension whenever
the retained suffix leaves too few places to block the internal neighbors. -/
theorem girth_six_grow_metric_suffix (hg : 6 ≤ G.egirth) (hc : G.Connected) (P : Chain G n)
    (S : Finset V) (u : S) (hu : P.vertex 0=u.val) (hn : 1 ≤ n) {t : ℕ}
    (hm : P.metricSuffix t) (room : (t-3)/2+4 < (G.induce (S : Set V)).degree u) :
    ∃ z∈S,Good P z := by
  classical
  by_contra! none
  let A := coreNeighbors (G:=G) S u
  let N := A.erase (P.vertex 1)
  have nc : A.card=(G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have er : A.card-1 ≤ N.card := Finset.pred_card_le_card_erase
  have mem (z) (hz : z∈N) := mem_coreNeighbors (Finset.mem_erase.mp hz).2
  let C := contacts_of_stall P hn hg N (fun z hz => hu ▸ (mem z hz).1)
    (fun z hz => (Finset.mem_erase.mp hz).1) (fun z hz => none _ (mem z hz).2)
  obtain ⟨_,_,upper,_⟩ := geodesic_slots hc P 0 (by decide)
    (fun i hi hin => ⟨(hm i hi hin).le,(hm i hi hin).ge⟩) C (fun z hz => hu ▸ (mem z hz).1)
  omega

omit [Fintype V] in
/-- The near and far clusters that can obstruct the other end of an
already extended geodesic each cost at most one neighbor per two indices. -/
theorem girth_six_grow_two_intervals (hg : 6 ≤ G.egirth) (hc : G.Connected) (P : Chain G n)
    (S : Finset V) (u : S) (hu : P.vertex 0=u.val) (hn : 1 ≤ n) {lo far : ℕ}
    (ranges : ∀ i ≤ n,G.dist (P.vertex 0) (P.vertex i) ≤ 2 → i ≤ lo ∨ far ≤ i)
    (room : (lo-2)/2+(n+2-far)/2+1 < (G.induce (S : Set V)).degree u) :
    ∃ z∈S,Good P z := by
  classical
  by_contra! none
  let A := coreNeighbors (G:=G) S u
  let N := A.erase (P.vertex 1)
  have nc : A.card=(G.induce (S : Set V)).degree u := coreNeighbors_card S u
  have er : A.card-1 ≤ N.card := Finset.pred_card_le_card_erase
  have mem (z) (hz : z∈N) := mem_coreNeighbors (Finset.mem_erase.mp hz).2
  let C := contacts_of_stall P hn hg N (fun z hz => hu ▸ (mem z hz).1)
    (fun z hz => (Finset.mem_erase.mp hz).1) (fun z hz => none _ (mem z hz).2)
  let f (i : ℕ) := if i ≤ lo then (i-4)/2 else (lo-2)/2+(i-far)/2
  have pos (w i) (h : C.touches w i) := ranges i (C.upper h)
    (near_contact hc (hu ▸ (mem w w.property).1) (C.adjacent h))
  have count := (C.slots f (m:=(lo-2)/2+(n+2-far)/2) (fun w i h => by
    have := C.lower h; have := C.upper h; have := pos w i h
    dsimp [f]; split_ifs <;> omega) (fun w z i j h h' eq => by
    have := C.lower h; have := C.lower h'; have := pos w i h; have := pos z j h'
    dsimp [f] at eq; split_ifs at eq <;> omega)).1
  omega

end Wall133
