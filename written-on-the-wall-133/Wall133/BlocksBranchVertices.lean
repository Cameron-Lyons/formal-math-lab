module

public import Wall133.BlocksBipartiteCore

@[expose] public section

/-! # Bipartiteness on vertices of degree at least three -/

namespace Wall133
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

private def ProperOn (G : SimpleGraph V) (S : Finset V) (f : V → Fin 2) : Prop :=
  ∀ {x y}, x ∈ S → y ∈ S → G.Adj x y → f x ≠ f y

omit [DecidableRel G.Adj] in
private theorem exists_maximal_proper {T : Finset V} (f₀ : V → Fin 2) (h₀ : ProperOn G T f₀) :
    ∃ S : Finset V, T ⊆ S ∧ ∃ f, ProperOn G S f ∧
      ∀ z ∉ S, ∀ g : V → Fin 2, ¬ ProperOn G (insert z S) g := by
  classical
  let sets := Finset.univ.filter (fun S : Finset V => T ⊆ S ∧ ∃ f, ProperOn G S f)
  have mem (S : Finset V) : S ∈ sets ↔ T ⊆ S ∧ ∃ f, ProperOn G S f := by simp [sets]
  obtain ⟨S,hS,high⟩ := sets.exists_max_image Finset.card ⟨T,(mem T).2 ⟨fun _ h => h, f₀,h₀⟩⟩
  obtain ⟨hTS,f,hf⟩ := (mem S).1 hS
  have maximal : ∀ z ∉ S, ∀ g : V → Fin 2, ¬ ProperOn G (insert z S) g := by
    intro z hz g hg
    have hmem := (mem (insert z S)).2 ⟨hTS.trans (Finset.subset_insert _ _),g,hg⟩
    have hh := high _ hmem
    rw [Finset.card_insert_of_notMem hz] at hh
    omega
  exact ⟨S,hTS,f,hf,maximal⟩

omit [Fintype V] in
private theorem maximal_coloring_hits {S : Finset V} (f : V → Fin 2) (hf : ProperOn G S f)
    (maximal : ∀ z ∉ S, ∀ g : V → Fin 2, ¬ ProperOn G (insert z S) g)
    {z : V} (hz : z ∉ S) (t : Fin 2) : ∃ a : S, f a.val = t ∧ G.Adj z a.val := by
  classical
  by_contra! hn
  let g (v : V) := if v = z then t else f v
  apply maximal z hz g
  intro x y hx hy hxy
  rcases Finset.mem_insert.mp hx with rfl | hxS
  · rcases Finset.mem_insert.mp hy with rfl | hyS
    · exact False.elim (G.irrefl hxy)
    · simpa [g,hxy.ne.symm] using
        (show t ≠ f y from fun e => hn ⟨y,hyS⟩ e.symm hxy)
  · rcases Finset.mem_insert.mp hy with rfl | hyS
    · simpa [g,hxy.ne] using (show f x ≠ t from fun e => hn ⟨x,hxS⟩ e hxy.symm)
    · simpa [g,show x ≠ z from fun e => hz (e ▸ hxS),show y ≠ z from fun e => hz (e ▸ hyS)]
        using hf hxS hyS hxy

private def flip (t : Fin 2) : Fin 2 := if t = 0 then 1 else 0

private theorem flip_injective : Function.Injective flip := by decide

private theorem connected_pair_of_maximal {S : Finset V}
    (f : V → Fin 2) (hf : ProperOn G S f)
    (maximal : ∀ z ∉ S, ∀ g : V → Fin 2, ¬ ProperOn G (insert z S) g)
    (low : ∀ z ∉ S, G.degree z ≤ 2) {z : V} (hz : z ∉ S) :
    ∃ a b : S, f a.val ≠ f b.val ∧ G.Adj z a.val ∧ G.Adj z b.val ∧
      (G.induce (S : Set V)).Reachable a b ∧
      ∀ w, G.Adj z w → w = a.val ∨ w = b.val := by
  classical
  let H := G.induce (S : Set V)
  obtain ⟨a,ha,hza⟩ := maximal_coloring_hits f hf maximal hz 0
  obtain ⟨b,hb,hzb⟩ := maximal_coloring_hits f hf maximal hz 1
  have hcol : f a.val ≠ f b.val := by rw [ha,hb]; decide
  have hab : a.val ≠ b.val := fun he => hcol (congrArg f he)
  have pair : ({a.val,b.val} : Finset V) = G.neighborFinset z := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | h
      · exact (G.mem_neighborFinset _ _).2 hza
      · exact (Finset.mem_singleton.mp h) ▸ (G.mem_neighborFinset _ _).2 hzb
    · rw [Finset.card_pair hab,G.card_neighborFinset_eq_degree]
      exact low z hz
  have in_pair (w : V) (hw : G.Adj z w) : w = a.val ∨ w = b.val := by
    have hh := (G.mem_neighborFinset z w).2 hw
    rw [←pair, Finset.mem_insert, Finset.mem_singleton] at hh
    exact hh
  refine ⟨a,b,hcol,hza,hzb,?_,in_pair⟩
  by_contra hn
  let inside (w : V) : Prop := ∃ x : S, x.val = w ∧ H.Reachable a x
  let g (w : V) : Fin 2 := if inside w then flip (f w) else f w
  have proper : ProperOn G S g := by
    intro v w hv hw hvw
    have pass {p q : V} (hp : p ∈ S) (hq : q ∈ S) (h : G.Adj p q) (hi : inside p) : inside q := by
      obtain ⟨x,rfl,hx⟩ := hi
      exact ⟨⟨q,hq⟩,rfl,hx.trans ((show H.Adj x ⟨q,hq⟩ from h).reachable)⟩
    by_cases hi : inside v
    · have hj := pass hv hw hvw hi
      simpa [g,hi,hj] using fun h : flip (f v) = flip (f w) =>
        hf hv hw hvw (flip_injective h)
    · have hj : ¬ inside w := fun h => hi (pass hw hv hvw.symm h)
      simpa [g,hi,hj] using hf hv hw hvw
  have ia : inside a.val := ⟨a,rfl,.refl _⟩
  have ob : ¬inside b.val := by
    rintro ⟨x,hx,hr⟩
    exact hn ((show x=b from Subtype.ext hx) ▸ hr)
  obtain ⟨w,hw,hzw⟩ := maximal_coloring_hits g proper maximal hz 0
  rcases in_pair w.val hzw with h | h
  · rw [h] at hw
    simp [g,ia,ha,flip] at hw
  · rw [h] at hw
    simp [g,ob,hb] at hw

/-- A connected graph whose vertices of degree at least three induce
a bipartite graph has a connected induced bipartite subgraph containing
all of them. Every omitted vertex has neighbors in both of its parts. -/
theorem exists_bipartite_core_of_bipartite_branch_vertices (hc : G.Connected)
    (hb : (G.induce {x | 3 ≤ G.degree x}).IsBipartite) :
    ∃ S : Finset V, (G.induce (S : Set V)).Connected ∧
      ∃ c : (G.induce (S : Set V)).Coloring (Fin 2),
        (∀ z ∉ S, G.degree z ≤ 2) ∧
        ∀ z ∉ S, ∃ a b : S, c a ≠ c b ∧ G.Adj z a.val ∧ G.Adj z b.val := by
  classical
  let T := Finset.univ.filter (fun x : V => 3 ≤ G.degree x)
  obtain ⟨c₀⟩ := hb
  let f₀ (x : V) : Fin 2 := if h : 3 ≤ G.degree x then c₀ ⟨x,h⟩ else 0
  have h₀ : ProperOn G T f₀ := by
    intro x y hx hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    simpa [f₀,hx',hy'] using c₀.valid (v := ⟨x,hx'⟩) (w := ⟨y,hy'⟩) hxy
  obtain ⟨S,hTS,f,hf,maximal⟩ := exists_maximal_proper f₀ h₀
  let H := G.induce (S : Set V)
  have low (z : V) (hz : z ∉ S) : G.degree z ≤ 2 := by
    by_contra! h
    exact hz (hTS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
  have pairs := fun z hz => connected_pair_of_maximal f hf maximal low (z := z) hz
  let rep (v : V) : S := if hv : v ∈ S then ⟨v,hv⟩ else (pairs v hv).choose
  have self (v : S) : rep v.val = v := by simp [rep,v.property]
  have transfer {z : V} (hz : z ∉ S) (w : S) (hw : G.Adj z w.val) : H.Reachable (rep z) w := by
    let a := (pairs z hz).choose
    obtain ⟨b,_,_,_,hr,ends⟩ := (pairs z hz).choose_spec
    rw [show rep z=a from dite_eq_right hz]
    rcases ends w.val hw with h | h
    · exact (show w=a from Subtype.ext h) ▸ .refl _
    · exact (show w=b from Subtype.ext h) ▸ hr
  have ends_in {z w : V} (hz : z ∉ S) (hw : G.Adj z w) : w ∈ S := by
    obtain ⟨a,b,_,_,_,_,ends⟩ := pairs z hz
    rcases ends w hw with rfl | rfl
    · exact a.property
    · exact b.property
  have preserve {v w : V} (h : G.Adj v w) : H.Reachable (rep v) (rep w) := by
    by_cases hv : v ∈ S
    · rw [self ⟨v,hv⟩]
      by_cases hw : w ∈ S
      · rw [self ⟨w,hw⟩]
        exact (show H.Adj ⟨v,hv⟩ ⟨w,hw⟩ from h).reachable
      · exact (transfer hw ⟨v,hv⟩ h.symm).symm
    · have hw := ends_in hv h
      rw [self ⟨w,hw⟩]
      exact transfer hv ⟨w,hw⟩ h
  have walk {v w : V} (p : G.Walk v w) : H.Reachable (rep v) (rep w) := by
    induction p with
    | nil => exact .refl _
    | cons h _ ih => exact (preserve h).trans ih
  let : Nonempty S := ⟨rep hc.nonempty.some⟩
  have hcH : H.Connected := ⟨fun u v => by
    simpa only [self] using walk (hc u.val v.val).some⟩
  let c : H.Coloring (Fin 2) := ⟨fun v => f v.val, fun {v w} h => hf v.property w.property h⟩
  refine ⟨S,hcH,c,low,?_⟩
  intro z hz
  obtain ⟨a,b,hc,ha,hb,_,_⟩ := pairs z hz
  exact ⟨a,b,hc,ha,hb⟩

/-- The floored bound holds at every radius for a bipartite induced graph
on the vertices of degree at least three, throughout the range of floors
at least four. -/
theorem radius_add_floor_le_path_of_bipartite_branch_vertices (hc : G.Connected)
    (h4 : NoFourCycle G) (hb : (G.induce {x | 3 ≤ G.degree x}).IsBipartite)
    (hk : 4 ≤ ⌊l G⌋₊) : G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  obtain ⟨S,hS,c,low,both⟩ := exists_bipartite_core_of_bipartite_branch_vertices hc hb
  apply radius_add_floor_le_path_of_bipartite_core hc h4 S hS c both
  have sum := Finset.sum_le_sum (s := Sᶜ) (f := fun z => G.degree z) (g := fun _ => 2)
    (fun z hz => low z (Finset.mem_compl.mp hz))
  simp only [Finset.sum_const,smul_eq_mul] at sum
  have := Nat.mul_le_mul_left Sᶜ.card hk
  omega


/-- A connected dominating induced bipartite graph can serve as a starting
set whenever twice the degree of every vertex outside it is at most the
floored neighborhood average. -/
theorem radius_add_floor_le_path_of_dominating_bipartite (hc : G.Connected)
    (h4 : NoFourCycle G) (T : Finset V) (hcT : (G.induce (T : Set V)).Connected)
    (hb : (G.induce (T : Set V)).IsBipartite)
    (dom : ∀ z ∉ T, ∃ a : T, G.Adj z a.val)
    (low : ∀ z ∉ T, 2 * G.degree z ≤ ⌊l G⌋₊) :
    G.radius.toNat + ⌊l G⌋₊ ≤ G.path := by
  classical
  obtain ⟨C⟩ := hb
  let f₀ (v : V) : Fin 2 := if h : v ∈ T then C ⟨v,h⟩ else 0
  have h₀ : ProperOn G T f₀ := by
    intro x y hx hy hxy
    simpa [f₀,hx,hy] using C.valid (v := ⟨x,hx⟩) (w := ⟨y,hy⟩) hxy
  obtain ⟨S,hTS,f,hf,maximal⟩ := exists_maximal_proper f₀ h₀
  let H := G.induce (S : Set V)
  let c : H.Coloring (Fin 2) := ⟨fun x => f x.val, fun {v w} h => hf v.property w.property h⟩
  let inc := (G.induceHomOfLE (s := (T : Set V)) (s' := (S : Set V)) hTS).toHom
  have access (u : S) : ∃ a : T, H.Reachable (inc a) u := by
    by_cases ht : u.val ∈ T
    · exact ⟨⟨u.val,ht⟩,.refl _⟩
    · obtain ⟨a,ha⟩ := dom u.val ht
      exact ⟨a,(show H.Adj (inc a) u from ha.symm).reachable⟩
  let : Nonempty S := ⟨inc hcT.nonempty.some⟩
  have hcS : H.Connected := by
    constructor
    intro u v
    obtain ⟨a,ha⟩ := access u
    obtain ⟨b,hb⟩ := access v
    exact ha.symm.trans (((hcT a b).map inc).trans hb)
  apply radius_add_floor_le_path_of_bipartite_core hc h4 S hcS c
  · intro z hz
    obtain ⟨a,ha,hza⟩ := maximal_coloring_hits f hf maximal hz 0
    obtain ⟨b,hb,hzb⟩ := maximal_coloring_hits f hf maximal hz 1
    exact ⟨a,b,show f a.val ≠ f b.val by rw [ha,hb]; decide,hza,hzb⟩
  · rw [Finset.mul_sum]
    simpa using Finset.sum_le_sum (s := Sᶜ) (g := fun _ => ⌊l G⌋₊)
      (fun x hx => low x (fun h => Finset.mem_compl.mp hx (hTS h)))

end Wall133
