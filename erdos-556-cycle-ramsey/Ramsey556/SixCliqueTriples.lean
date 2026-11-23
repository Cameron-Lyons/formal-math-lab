import Ramsey556.SixClique
import Ramsey556.ThreeShore

namespace Ramsey556.SixClique

/-- Unordered two- and three-element subsets of the six anchor positions. -/
def pairVertices : Vector (Fin 6 × Fin 6) 15 := #v[(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

def tripleVertices : Vector (Vector (Fin 6) 3) 20 := #v[
  #v[0,1,2],#v[0,1,3],#v[0,1,4],#v[0,1,5],#v[0,2,3],
  #v[0,2,4],#v[0,2,5],#v[0,3,4],#v[0,3,5],#v[0,4,5],
  #v[1,2,3],#v[1,2,4],#v[1,2,5],#v[1,3,4],#v[1,3,5],
  #v[1,4,5],#v[2,3,4],#v[2,3,5],#v[2,4,5],#v[3,4,5]]

private def deleteOne : Vector (Vector (Fin 15) 3) 20 := #v[
  #v[0,1,5],#v[0,2,6],#v[0,3,7],#v[0,4,8],#v[1,2,9],
  #v[1,3,10],#v[1,4,11],#v[2,3,12],#v[2,4,13],#v[3,4,14],
  #v[5,6,9],#v[5,7,10],#v[5,8,11],#v[6,7,12],#v[6,8,13],
  #v[7,8,14],#v[9,10,12],#v[9,11,13],#v[10,11,14],#v[12,13,14]]

private def share (p q : Fin 15) : Bool :=
  let (a,b) := pairVertices[p]
  let (c,d) := pairVertices[q]
  a==c || a==d || b==c || b==d

private def allowed (p q r : Fin 15) : Bool :=
  p==q || p==r || q==r || (share p q && share p r && share q r)

private theorem distinctSlots (p q : Fin 15) : share p q = false →
    [pairVertices[p].1,pairVertices[p].2,pairVertices[q].1,pairVertices[q].2].Nodup := by
  revert p q; decide +kernel

private theorem endsDistinct : ∀ p : Fin 15, pairVertices[p].1 ≠ pairVertices[p].2 := by decide
private theorem indicesEq : ∀ p q : Fin 15,
    ((pairVertices[p].1=pairVertices[q].1 ∧ pairVertices[p].2=pairVertices[q].2) ∨
      (pairVertices[p].1=pairVertices[q].2 ∧ pairVertices[p].2=pairVertices[q].1)) → p=q := by decide

private def UsesPair {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n) (x : Fin n) (p : Fin 15) : Prop :=
  c.edge x (A pairVertices[p].1)=k ∧ c.edge x (A pairVertices[p].2)=k

private theorem allowed_of_free {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n)
    (X : Fin 3 → Fin n) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (xi : ∀ ⦃i j⦄, X i=X j → i=j)
    (apart : ∀ i j, A i≠X j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=k)
    (free : ¬HasMonoC9 c) (p q r : Fin 15)
    (h0 : UsesPair c k A (X 0) p) (h1 : UsesPair c k A (X 1) q) (h2 : UsesPair c k A (X 2) r) :
    allowed p q r = true := by
  have one (i j z : Fin 3) (positions : [i,j,z].Nodup) (P Q R : Fin 15)
      (hp : UsesPair c k A (X i) P) (hq : UsesPair c k A (X j) Q) (hr : UsesPair c k A (X z) R)
      (missing : share P Q=false) : R=P ∨ R=Q := by
    let index (v : Fin 3) := [i,j,z][v.val]'v.isLt
    let Y (v : Fin 3) := X (index v)
    have yi : ∀ ⦃a b⦄, Y a=Y b → a=b :=
      fun {_ _} e => Fin.ext (positions.eq_of_getElem_eq _ _ (xi e))
    obtain h|h := Forest.disjoint_pairs c k A Y (@ai) (@yi) (fun _ _ => apart _ _) clique free
      (distinctSlots _ _ missing) (endsDistinct R) hp.1 hp.2 hq.1 hq.2 hr.1 hr.2
    · exact Or.inl (indicesEq _ _ h)
    · exact Or.inr (indicesEq _ _ h)
  by_cases a : p=q
  · simp [allowed,a]
  by_cases b : p=r
  · simp [allowed,b]
  by_cases d : q=r
  · simp [allowed,d]
  have pq : share p q = true := by
    apply Bool.eq_true_of_ne_false
    intro h; rcases one 0 1 2 (by decide) p q r h0 h1 h2 h with e|e <;> grind
  have pr : share p r = true := by
    apply Bool.eq_true_of_ne_false
    intro h; rcases one 0 2 1 (by decide) p r q h0 h2 h1 h with e|e <;> grind
  have qr : share q r = true := by
    apply Bool.eq_true_of_ne_false
    intro h; rcases one 1 2 0 (by decide) q r p h1 h2 h0 h with e|e <;> grind
  simp [allowed,pq,pr,qr]

private theorem delete_mem : ∀ (t : Fin 20) (i : Fin 3),
    (∃ j : Fin 3, pairVertices[deleteOne[t][i]].1=tripleVertices[t][j]) ∧
    (∃ j : Fin 3, pairVertices[deleteOne[t][i]].2=tripleVertices[t][j]) := by decide +kernel

set_option maxHeartbeats 0 in
private theorem classifyTriples : ∀ (t w : Fin 20) (p : Fin 15),
    (∀ i j : Fin 3, allowed (deleteOne[t][i]) (deleteOne[w][j]) p = true) →
      t=w ∧ (∃ j : Fin 3, pairVertices[p].1=tripleVertices[t][j]) ∧
           (∃ j : Fin 3, pairVertices[p].2=tripleVertices[t][j]) := by decide +kernel

/-- Two exterior vertices each seeing a triple in the six-clique must see
the same triple, provided a third exterior vertex sees at least two anchors.
Both neighbors of that third vertex belong to the common triple. -/
theorem common_triple {n : Nat} (c : Coloring n) (k : Fin 3) (A : Fin 6 → Fin n)
    (X : Fin 3 → Fin n) (ai : ∀ ⦃i j⦄, A i=A j → i=j) (xi : ∀ ⦃i j⦄, X i=X j → i=j)
    (apart : ∀ i j, A i≠X j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=k)
    (free : ¬HasMonoC9 c) (t w : Fin 20) (p : Fin 15)
    (left : ∀ i : Fin 3, c.edge (X 0) (A tripleVertices[t][i])=k)
    (right : ∀ i : Fin 3, c.edge (X 1) (A tripleVertices[w][i])=k)
    (first : c.edge (X 2) (A pairVertices[p].1)=k) (last : c.edge (X 2) (A pairVertices[p].2)=k) :
    t=w ∧ (∃ j : Fin 3, pairVertices[p].1=tripleVertices[t][j]) ∧
          (∃ j : Fin 3, pairVertices[p].2=tripleVertices[t][j]) := by
  have use (z : Fin 3) (T : Fin 20) (h : ∀ i : Fin 3, c.edge (X z) (A tripleVertices[T][i])=k)
      (i : Fin 3) : UsesPair c k A (X z) (deleteOne[T][i]) := by
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := delete_mem T i
    exact ⟨by rw [ha]; exact h a, by rw [hb]; exact h b⟩
  apply classifyTriples t w p
  intro i j
  exact allowed_of_free c k A X (@ai) (@xi) apart clique free _ _ _ (use 0 t left i) (use 1 w right j) ⟨first,last⟩

private theorem enumeratePair : ∀ a b : Fin 6, a≠b → ∃ p : Fin 15,
    (a=pairVertices[p].1 ∧ b=pairVertices[p].2) ∨ (a=pairVertices[p].2 ∧ b=pairVertices[p].1) := by decide

private theorem enumeratePairWith (a : Fin 6) (p : Fin 15) : ∃ q : Fin 15,
    (a=pairVertices[q].1 ∨ a=pairVertices[q].2) ∧
    (∀ z ∈ [pairVertices[q].1,pairVertices[q].2], z=a ∨ z=pairVertices[p].1 ∨ z=pairVertices[p].2) := by
  revert a p; decide +kernel

private theorem enlargeTriple : ∀ (t : Fin 20) (a : Fin 6),
    (∀ j : Fin 3, a≠tripleVertices[t][j]) → ∃ w : Fin 20, w≠t ∧
      ∀ j : Fin 3, tripleVertices[w][j]=a ∨ ∃ z : Fin 3, tripleVertices[w][j]=tripleVertices[t][z] := by decide +kernel

private theorem otherTriple : ∀ t : Fin 20, ∃ w : Fin 20,
    ∀ i j : Fin 3, tripleVertices[w][i] ≠ tripleVertices[t][j] := by decide +kernel

private theorem tripleInj : ∀ (t : Fin 20) (i j : Fin 3),
    tripleVertices[t][i] = tripleVertices[t][j] → i=j := by decide

private theorem deletedDiffer : ∀ t : Fin 20, deleteOne[t][0] ≠ deleteOne[t][1] := by decide

/-- Eleven exterior vertices cannot all avoid blue and each see two green
neighbors in a green six-clique if two of them each see a green triple.
The common triple leaves a red K₃,₁₁. Any red-independent nine vertices
of its large shore would be a blue clique. -/
theorem eleven_rich {n : Nat} (c : Coloring n) (red green blue : Fin 3)
    (rg : red≠green) (rb : red≠blue) (gb : green≠blue)
    (A : Fin 6 → Fin n) (E : Fin 11 → Fin n)
    (ai : ∀ ⦃i j⦄, A i=A j → i=j) (ei : ∀ ⦃i j⦄, E i=E j → i=j)
    (away : ∀ i j, A i≠E j) (clique : ∀ i j, i≠j → c.edge (A i) (A j)=green)
    (noBlue : ∀ i j, c.edge (E i) (A j)≠blue)
    (rich : ∀ i, ∃ a b, a≠b ∧ c.edge (E i) (A a)=green ∧ c.edge (E i) (A b)=green)
    (t w : Fin 20) (left : ∀ j : Fin 3, c.edge (E 0) (A tripleVertices[t][j])=green)
    (right : ∀ j : Fin 3, c.edge (E 1) (A tripleVertices[w][j])=green) : HasMonoC9 c := by
  apply Classical.byContradiction; intro free
  let uses (i : Fin 11) (p : Fin 15) := UsesPair c green A (E i) p
  let sees (i : Fin 11) (T : Fin 20) := ∀ j : Fin 3, c.edge (E i) (A tripleVertices[T][j])=green
  have somePair (i) : ∃ p, uses i p := by
    obtain ⟨a,b,ne,ha,hb⟩ := rich i
    obtain ⟨p,h|h⟩ := enumeratePair a b ne
    · exact ⟨p, h.1 ▸ ha, h.2 ▸ hb⟩
    · exact ⟨p, h.2 ▸ hb, h.1 ▸ ha⟩
  let vec (i j k : Fin 11) (z : Fin 3) := [i,j,k][z.val]'z.isLt
  have vi {i j k : Fin 11} (nd : [i,j,k].Nodup) : ∀ ⦃a b⦄, E (vec i j k a)=E (vec i j k b) → a=b :=
    fun {_ _} h => Fin.ext (nd.eq_of_getElem_eq _ _ (ei h))
  have same (i j k : Fin 11) (nd : [i,j,k].Nodup) {T W P} (hT : sees i T) (hW : sees j W) (hP : uses k P) :=
    common_triple c green A (fun z => E (vec i j k z)) (@ai) (@vi _ _ _ nd) (fun _ _ => away _ _) clique
      free T W P hT hW hP.1 hP.2
  obtain ⟨p2,h2⟩ := somePair 2
  have tw := (same 0 1 2 (by decide) left right h2).1
  subst w
  have only (i : Fin 11) (a : Fin 6) (outside : ∀ j : Fin 3, a≠tripleVertices[t][j]) :
      c.edge (E i) (A a)≠green := by
    intro ha
    by_cases e0 : i=0
    · subst i
      obtain ⟨W,ne,subset⟩ := enlargeTriple t a outside
      have usesW : sees 0 W := by
        intro j
        rcases subset j with eq|⟨z,eq⟩
        · rwa [eq]
        · rw [eq]; exact left z
      exact ne (same 0 1 2 (by decide) usesW right h2).1
    by_cases e1 : i=1
    · subst i
      obtain ⟨W,ne,subset⟩ := enlargeTriple t a outside
      have usesW : sees 1 W := by
        intro j
        rcases subset j with eq|⟨z,eq⟩
        · rwa [eq]
        · rw [eq]; exact right z
      exact ne (same 1 0 2 (by decide) usesW left h2).1
    obtain ⟨P,hP⟩ := somePair i
    obtain ⟨Q,inc,sub⟩ := enumeratePairWith a P
    have inQ (z : Fin 6) (mem : z ∈ [pairVertices[Q].1,pairVertices[Q].2]) :
        c.edge (E i) (A z)=green := by
      rcases sub z mem with eq|eq|eq
      · rwa [eq]
      · exact eq ▸ hP.1
      · exact eq ▸ hP.2
    have hQ : uses i Q := ⟨inQ _ (by simp),inQ _ (by simp)⟩
    obtain ⟨_,⟨a1,hit1⟩,⟨a2,hit2⟩⟩ := same 0 1 i (by simp; omega) left right hQ
    rcases inc with eq|eq
    · exact outside a1 (eq.trans hit1)
    · exact outside a2 (eq.trans hit2)
  have noGreen (i j : Fin 11) (ne : i≠j) : c.edge (E i) (E j)≠green := by
    intro edge
    have eqPair (k : Fin 11) (nd : [i,j,k].Nodup) (p q r : Fin 15)
        (hp : uses i p) (hq : uses j q) (hr : uses k r) : p=r ∧ q=r := by
      have eq := linked_pairs c green A (fun a => E (vec i j k a)) (@ai) (@vi _ _ _ nd)
        (fun _ _ => away _ _) clique free edge (endsDistinct p) (endsDistinct q) (endsDistinct r)
        hp.1 hp.2 hq.1 hq.2 hr.1 hr.2
      exact ⟨indicesEq _ _ eq.1,indicesEq _ _ eq.2⟩
    obtain ⟨P,hP⟩ := somePair i
    obtain ⟨Q,hQ⟩ := somePair j
    have fixed (k : Fin 11) (R : Fin 15) (hR : uses k R) : P=R := by
      obtain ⟨l,other⟩ := (by decide : ∀ i j : Fin 11, i≠j → ∃ l, [i,j,l].Nodup) i j ne
      obtain ⟨L,hL⟩ := somePair l
      by_cases hi : k=i
      · subst k; exact (eqPair l other P Q L hP hQ hL).1.trans (eqPair l other R Q L hR hQ hL).1.symm
      by_cases hj : k=j
      · subst k; exact (eqPair l other P Q L hP hQ hL).1.trans (eqPair l other P R L hP hR hL).2.symm
      exact (eqPair k (by simp; grind) P Q R hP hQ hR).1
    have inside (z : Fin 3) : uses 0 (deleteOne[t][z]) := by
      obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := delete_mem t z
      exact ⟨by rw [ha]; exact left a,by rw [hb]; exact left b⟩
    exact deletedDiffer t ((fixed 0 _ (inside 0)).symm.trans (fixed 0 _ (inside 1)))
  obtain ⟨U,disj⟩ := otherTriple t
  apply free
  apply BicliqueObstruction.hasMonoC9_of_three_shore_on (m:=9) c red (by decide)
    (fun i => A tripleVertices[U][i]) E (fun {_ _} h => tripleInj _ _ _ (ai h)) (@ei) (fun _ _ => away _ _)
  · intro i j
    have ng := only j _ (disj i)
    have nb := noBlue j tripleVertices[U][i]
    rw [c.symm]
    omega
  · intro f fi contained
    apply Classical.byContradiction; intro none
    apply free
    refine ⟨blue,f,@fi,?_⟩
    intro i
    have diff : i≠i+1 := (by decide : ∀ k : Fin 9, k≠k+1) i
    obtain ⟨j,hj⟩ := contained i
    obtain ⟨k,hk⟩ := contained (i+1)
    have jk : j≠k := fun eq => diff (fi (hj.trans ((congrArg E eq).trans hk.symm)))
    have ng : c.edge (f i) (f (i+1))≠green := by rw [hj,hk]; exact noGreen _ _ jk
    have nr : c.edge (f i) (f (i+1))≠red := fun h => none ⟨i,i+1,diff,h⟩
    omega

end Ramsey556.SixClique
