import Ramsey556.Split17.Catalog
import Ramsey556.Split17.Proofs

namespace Ramsey556.Split17

/-- Two-color the edges of K₁₇ outside a specified four-vertex set. These
edges already contain a monochromatic C₉, regardless of the six omitted edges. -/
theorem hasMonoC9 {n : Nat} (c : Coloring n) (r s : Fin 3) (ne : r ≠ s) (v : Fin 17 → Fin n)
    (inj : ∀ ⦃i j⦄, v i = v j → i = j)
    (uses : ∀ i j, i ≠ j → (i.val < 13 ∨ j.val < 13) → c.edge (v i) (v j) = r ∨ c.edge (v i) (v j) = s) :
    HasMonoC9 c := by
  apply Classical.byContradiction
  intro free
  let first (i : Fin 14) : Fin 17 := ⟨i.val,by omega⟩
  have fi : ∀ ⦃i j⦄, first i = first j → i = j := fun {_ _} e => Fin.ext (congrArg (fun t : Fin 17 => t.val) e)
  let d := c.induce (fun i => v (first i))
  have dUses (i j : Fin 14) (ij : i ≠ j) : d.edge i j = r ∨ d.edge i j = s := by
    apply uses _ _ (fun e => ij (fi e))
    change i.val < 13 ∨ j.val < 13
    omega
  have df : ¬ HasMonoC9 d := by
    rintro ⟨k,p,pi,he⟩
    exact free ⟨k,fun i => v (first (p i)),fun {_ _} e => pi (fi (inj e)),he⟩
  obtain ⟨t,a,b,f,palette,perm,pattern⟩ := classify14 d r s ne dUses df
  obtain ⟨inv,right,_⟩ := Cert16.inverse_exists f (@perm)
  let mark := inv 13
  obtain ⟨q,flip,u,ui,away,base⟩ := trim14 t mark
  have lo (i : Fin 13) : (f (u i)).val < 13 := by
    have sep : f (u i) ≠ 13 := fun e => away i (perm (e.trans (right 13).symm))
    omega
  let idx (i : Fin 17) : Fin 17 :=
    if h : i.val < 13 then first (f (u ⟨i.val,h⟩)) else i
  have idxInj : ∀ ⦃i j⦄, idx i = idx j → i = j := by
    intro i j eq
    dsimp only [idx] at eq
    split at eq <;> split at eq
    · exact Fin.ext (congrArg (fun x : Fin 13 => x.val) (ui (perm (fi eq))))
    · rename_i h _
      have low := lo ⟨i.val,h⟩
      have e := congrArg Fin.val eq
      dsimp [first] at e
      omega
    · rename_i _ h
      have low := lo ⟨j.val,h⟩
      have e := congrArg Fin.val eq
      dsimp [first] at e
      omega
    · exact eq
  let color (bit : Bool) := if (if flip then !bit else bit) then a else b
  have invert {k : Fin 3} (h : k = r ∨ k = s) : k = color false ∨ k = color true := by
    rcases palette with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> cases flip <;> simp [color] at * <;> grind
  apply free
  apply eliminate_core c (fun i => v (idx i)) color (fun {_ _} e => idxInj (inj e)) q
  · intro i j hi hj ij
    let x : Fin 13 := ⟨i.val,hi⟩
    let y : Fin 13 := ⟨j.val,hj⟩
    have xy : x ≠ y := fun e => ij (Fin.ext (congrArg (fun z : Fin 13 => z.val) e))
    have e := pattern (u x) (u y) (fun h => xy (ui h))
    change d.edge (f (u x)) (f (u y)) = (if Cert16.edge (core14 t) (u x).val (u y).val then a else b) at e
    rw [base x y xy] at e
    simpa only [idx,hi,hj,↓reduceDIte,x,y,d,Coloring.induce,color] using e
  · intro i j hi hj
    apply invert
    have low : (idx i).val < 13 := by simpa only [idx,hi,↓reduceDIte,first] using lo ⟨i.val,hi⟩
    apply uses (idx i) (idx j) (fun eq => ?_) (Or.inl low)
    exact (show i ≠ j by intro h; subst j; omega) (idxInj eq)

end Ramsey556.Split17
