import Wall133.OddRadiusFive

namespace Wall133
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

private theorem bad_second_extension (P : Chain G 9) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {x y z : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (hd : 4 ≤ G.degree z) (hshort : ¬13 ≤ G.path) :
    (∃ g, G.Adj z g ∧ G.Adj (P.vertex 2) g ∧ G.Adj (P.vertex 6) g) ∧
    (∃ a, G.Adj z a ∧ Off P a (· = 4)) ∧ (∃ b, G.Adj z b ∧ Off P b (· = 8)) := by
  let Q := grow (grow P x hx) z hz
  have sat (w : V) : ¬Good Q w := fun hw => hshort (grow Q w hw).length_le
  have witness (i : Fin 5) (hi : 1 ≤ i.val) (hp : PrivateContact Q i) :
      ∃ b, G.Adj z b ∧ Off P b (· = 2*i.val) :=
    contactOnSuffix P Q (r := 2) (by decide) (by omega) (by have := i.isLt; omega)
      (by decide) (fun _ _ => rfl)
      (fun j hj h => False.elim (hz.2.2 (j+1) (by omega) (by omega) h)) i rfl hp
  have np1 : ¬PrivateContact Q 1 := by
    intro hp
    obtain ⟨u,hzu,hu⟩ := witness 1 (by decide) hp
    exact hshort (path_of_private_end P c h4 (by decide) hx hy hxy hz hzu 2
      (Or.inl rfl) hu.fresh hu.contact)
  have noPair (j k : Fin 5) (hj : 1 ≤ j.val) (hk : k.val = j.val+1) :
      ¬(PrivateContact Q j ∧ PrivateContact Q k) :=
    fun ⟨pj,pk⟩ => hshort (path_of_two_step_pair P c h4 hx hy hxy hz j k hj hk pj pk)
  obtain ⟨a,b,hshared,hp⟩ := near_saturation_with_witness Q c h4 (by decide)
    (by change 5 ≤ G.degree z+1; omega) sat
  have h1 : a=1 ∨ b=1 := by
    by_contra! h
    exact np1 (hp 1 (Ne.symm h.1) (Ne.symm h.2))
  have h3 : a=3 ∨ b=3 := by
    by_contra! h
    have p3 := hp 3 (Ne.symm h.1) (Ne.symm h.2)
    have h2 : a=2 ∨ b=2 := by
      by_contra! hh
      exact noPair 2 3 (by decide) rfl ⟨hp 2 (Ne.symm hh.1) (Ne.symm hh.2),p3⟩
    have h4' : a=4 ∨ b=4 := by
      by_contra! hh
      exact noPair 3 4 (by decide) rfl ⟨p3,hp 4 (Ne.symm hh.1) (Ne.symm hh.2)⟩
    rcases h1 with rfl | rfl <;> rcases h2 with h|h <;> rcases h4' with h'|h' <;> simp_all
  have hab : (a=1 ∧ b=3) ∨ (a=3 ∧ b=1) := by
    rcases h1 with rfl|rfl <;> rcases h3 with h|h <;> simp_all
  rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals obtain he|⟨g,hzg,hg1,hg2⟩ := hshared
  all_goals first | contradiction |
    exact ⟨⟨g,hzg,hg1,hg2⟩, witness 2 (by decide) (hp 2 (by decide) (by decide)),
      witness 4 (by decide) (hp 4 (by decide) (by decide))⟩ |
    exact ⟨⟨g,hzg,hg2,hg1⟩, witness 2 (by decide) (hp 2 (by decide) (by decide)),
      witness 4 (by decide) (hp 4 (by decide) (by decide))⟩

private def gadget (P : Chain G 9) (x z b a z' : V) : ℕ → V
  | 0 => P.vertex 2
  | 1 => P.vertex 1
  | 2 => P.vertex 0
  | 3 => x
  | 4 => z
  | 5 => b
  | 6 => P.vertex 8
  | 7 => P.vertex 7
  | 8 => P.vertex 6
  | 9 => P.vertex 5
  | 10 => P.vertex 4
  | 11 => a
  | _ => z'

/-- Two unsuccessful second-step detours share a common neighbor and give
a thirteen-vertex path by traversing opposite portions of the original path. -/
theorem odd_four_two_deep_rows (P : Chain G 9) (c : G.Coloring (Fin 2))
    (h4 : NoFourCycle G) {x y z z' : V} (hx : Good P x) (hy : Good P y) (hxy : x ≠ y)
    (hz : Good (grow P x hx) z) (hz' : Good (grow P y hy) z')
    (hd : 4 ≤ G.degree z) (hd' : 4 ≤ G.degree z') : 13 ≤ G.path := by
  by_contra hshort
  obtain ⟨⟨g,hzg,h2g,h6g⟩,_,b,hzb,hb⟩ := bad_second_extension P c h4 hx hy hxy hz hd hshort
  obtain ⟨⟨g',hzg',h2g',h6g'⟩,⟨a,hza,ha⟩,_⟩ := bad_second_extension P c h4 hy hx hxy.symm hz' hd' hshort
  have h26 : P.vertex 2 ≠ P.vertex 6 := fun e => by
    have h := P.inj (by decide) (by decide) e
    contradiction
  have he := h4 h26 h2g h6g h2g' h6g'
  subst g'
  have hzx : G.Adj x z := hz.1
  have hzy : G.Adj y z' := hz'.1
  have h0z : z ≠ P.vertex 0 := hz.2.1 1 (by decide)
  have h0z' : z' ≠ P.vertex 0 := hz'.2.1 1 (by decide)
  have hxz' : ¬G.Adj x z' := fun e => h0z' (h4 hxy e hzy hx.1.symm hy.1.symm)
  have hzz : z ≠ z' := fun e => hxz' (e ▸ hzx)
  have hga : g ≠ a := fun e => by have := (ha.contact 2 (by decide)).1 (e ▸ h2g.symm); contradiction
  have hgb : g ≠ b := fun e => by have := (hb.contact 2 (by decide)).1 (e ▸ h2g.symm); contradiction
  have hza' : ¬ G.Adj z a := fun e => hga (h4 hzz hzg hzg' e hza)
  have hzb' : ¬ G.Adj z' b := fun e => hgb (h4 hzz hzg hzg' hzb e)
  have ca : c a = c x := (color_common c hza.symm hzy).trans (color_common c hy.1.symm hx.1.symm)
  have cb : c b = c x := color_common c hzb.symm hzx
  have cz : c z = c z' := color_common c hzg hzg'
  have na {u v : V} (h : c u = c v) : ¬G.Adj u v := fun e => c.valid e h
  have ox := offGood hx
  have off {w t : V} {hw : Good P w} (hh : Good (grow P w hw) t) : Off P t (fun _ => False) :=
    ⟨fun i hi => hh.2.1 (i+1) (by omega), fun i hi => iff_false_intro (hh.2.2 (i+1) (by omega) (by omega))⟩
  have oz := off hz
  have oz' := off hz'
  have rev {s : ℕ → Prop} {v : V} (h : Off P v s) (i : ℕ) (hi : i ≤ 9) :
      G.Adj (P.vertex i) v ↔ s i := (G.adj_comm _ _).trans (h.contact i hi)
  let f := gadget P x z b a z'
  have edges {i j} (hi : i ≤ 12) (hj : j ≤ 12) :
      G.Adj (f i) (f j) ↔ i+1=j ∨ j+1=i := by
    interval_cases i <;> interval_cases j <;>
      simp (disch := decide) [f,gadget,P.edges,ox.contact,oz.contact,oz'.contact,ha.contact,hb.contact,
        rev ox,rev oz,rev oz',rev ha,rev hb,hzx,hzx.symm,hzb,hzb.symm,hza,hza.symm,
        hxz',mt Adj.symm hxz',hza',mt Adj.symm hza',hzb',mt Adj.symm hzb',na ca,na ca.symm,
        na cb,na cb.symm,na (ca.trans cb.symm),na (cb.trans ca.symm),na cz,na cz.symm]
  let D : Chain G 12 := ⟨f,by
    intro i j hi hj h
    have twins : ∀ i j : Fin 13, (∀ k : Fin 13,
        (i.val+1=k.val ∨ k.val+1=i.val) ↔ (j.val+1=k.val ∨ k.val+1=j.val)) → i=j := by decide
    apply congrArg Fin.val (twins ⟨i,by omega⟩ ⟨j,by omega⟩ ?_)
    intro k
    have hk : k.val ≤ 12 := by omega
    exact (edges hi hk).symm.trans ((congrArg (fun v => G.Adj v (f k.val)) h).to_iff.trans (edges hj hk)),
    edges⟩
  exact hshort D.length_le

end Wall133
