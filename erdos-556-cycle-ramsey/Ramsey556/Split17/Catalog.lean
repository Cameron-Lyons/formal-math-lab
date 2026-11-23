import Ramsey556.Split17.Data
import Ramsey556.Fourteen

namespace Ramsey556.Split17

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private structure Relabel (n : Nat) where
  flip : Bool
  shape : Fin n
  labels : Nat

private def label {n m : Nat} (w : Relabel n) (i : Fin m) : Fin 14 :=
  ⟨((w.labels >>> (4*i.val)) % 16) % 14, Nat.mod_lt _ (by decide)⟩

/-- Vertex and color relabelings between the clique-and-star templates and
the numbering used in the split-graph certificate. Each row is in star-size order. -/
private def encodings (wide : Bool) : Vector (Relabel 14) 7 :=
  if wide then #v[
    ⟨true,9,0x76d5c4b3a29180⟩, ⟨true,11,0x76d5c4b3a29180⟩, ⟨true,13,0x76d5c4b3a29180⟩,
    ⟨false,3,0xdcba9876543210⟩, ⟨false,2,0xdcba9876543210⟩,
    ⟨false,1,0xdcba9876543210⟩, ⟨false,0,0xdcba9876543210⟩]
  else #v[
    ⟨true,7,0xd6c5b4a3928170⟩, ⟨true,8,0x75d4c3b2a19086⟩,
    ⟨true,10,0x6d5c4b3a291807⟩, ⟨true,12,0x6d5c4b3a291807⟩,
    ⟨false,6,0xdcba9876543210⟩, ⟨false,5,0xdcba9876543210⟩, ⟨false,4,0xdcba9876543210⟩]

private theorem encoding_ok : ∀ wide (t : Fin 7),
    let w := (encodings wide)[t]
    (∀ i j : Fin 14, label w i = label w j → i = j) ∧
    ∀ i j : Fin 14, i ≠ j → template14 wide t.castSucc (label w i) (label w j) =
      (if w.flip then !(Cert16.edge (core14 w.shape) i.val j.val) else Cert16.edge (core14 w.shape) i.val j.val) := by
  decide +kernel

theorem classify14 (c : Coloring 14) (r s : Fin 3) (ne : r ≠ s)
    (uses : ∀ i j, i ≠ j → c.edge i j = r ∨ c.edge i j = s) (free : ¬ HasMonoC9 c) :
    CriticalTemplates.Matches (fun t (i j : Fin 14) => Cert16.edge (core14 t) i.val j.val) c r s := by
  obtain ⟨wide,t,a,b,v,small,palette,vi,edges⟩ := Fourteen.classify c r s ne uses free
  obtain ⟨t,rfl⟩ : ∃ t' : Fin 7, t = t'.castSucc := ⟨⟨t.val,by omega⟩,rfl⟩
  let w := (encodings wide)[t]
  obtain ⟨inj,pattern⟩ := encoding_ok wide t
  refine ⟨w.shape, if w.flip then b else a, if w.flip then a else b, v ∘ label w, ?_,
    fun {_ _} h => inj _ _ (vi h), ?_⟩
  · rcases palette with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases w.flip <;> simp
  · intro i j neq
    apply (edges (label w i) (label w j) (fun eq => neq (inj i j eq))).trans
    rw [pattern i j neq]
    exact (by decide : ∀ (flip bit : Bool) (x y : Fin 3),
      (if (if flip then !bit else bit) then x else y) =
        (if bit then (if flip then y else x) else (if flip then x else y))) w.flip _ a b

private def trims : Vector (Relabel 18) 196 := #v[
  ⟨true,0,0x65432dcba9817⟩, ⟨true,0,0x65432dcba9807⟩, ⟨true,0,0x65431dcba9807⟩,
  ⟨true,0,0x65421dcba9807⟩, ⟨true,0,0x65321dcba9807⟩, ⟨true,0,0x64321dcba9807⟩,
  ⟨true,0,0x54321dcba9807⟩, ⟨true,1,0xdcba986543210⟩, ⟨true,2,0xdcba965432107⟩,
  ⟨true,2,0xdcba865432107⟩, ⟨true,2,0xdcb9865432107⟩, ⟨true,2,0xdca9865432107⟩,
  ⟨true,2,0xdba9865432107⟩, ⟨true,2,0xcba9865432107⟩, ⟨true,3,0xdcba986543217⟩,
  ⟨true,3,0xdcba986543207⟩, ⟨true,3,0xdcba986543107⟩, ⟨true,3,0xdcba986542107⟩,
  ⟨true,3,0xdcba986532107⟩, ⟨true,3,0xdcba986432107⟩, ⟨true,3,0xdcba985432107⟩,
  ⟨true,1,0xdcba986543210⟩, ⟨true,4,0xdcba965432107⟩, ⟨true,4,0xdcba865432107⟩,
  ⟨true,4,0xdcb9865432107⟩, ⟨true,4,0xdca9865432107⟩, ⟨true,4,0xdba9865432107⟩,
  ⟨true,2,0xcba9865432107⟩, ⟨true,5,0xdc654321ba987⟩, ⟨true,5,0xdc654320ba987⟩,
  ⟨true,5,0xdc654310ba987⟩, ⟨true,5,0xdc654210ba987⟩, ⟨true,5,0xdc653210ba987⟩,
  ⟨true,5,0xdc643210ba987⟩, ⟨true,5,0xdc543210ba987⟩, ⟨true,1,0xdcba986543210⟩,
  ⟨true,6,0xdcba965432107⟩, ⟨true,6,0xdcba865432107⟩, ⟨true,6,0xdcb9865432107⟩,
  ⟨true,6,0xdca9865432107⟩, ⟨true,4,0xdba9865432107⟩, ⟨true,4,0xcba9865432107⟩,
  ⟨true,7,0xdcb654321a987⟩, ⟨true,7,0xdcb654320a987⟩, ⟨true,7,0xdcb654310a987⟩,
  ⟨true,7,0xdcb654210a987⟩, ⟨true,7,0xdcb653210a987⟩, ⟨true,7,0xdcb643210a987⟩,
  ⟨true,7,0xdcb543210a987⟩, ⟨true,1,0xdcba986543210⟩, ⟨true,8,0xdcba965432107⟩,
  ⟨true,8,0xdcba865432107⟩, ⟨true,8,0xdcb9865432107⟩, ⟨true,6,0xdca9865432107⟩,
  ⟨true,6,0xdba9865432107⟩, ⟨true,6,0xcba9865432107⟩, ⟨true,9,0x54321dcba9876⟩,
  ⟨true,9,0x54320dcba9876⟩, ⟨true,9,0x54310dcba9876⟩, ⟨true,9,0x54210dcba9876⟩,
  ⟨true,9,0x53210dcba9876⟩, ⟨true,9,0x43210dcba9876⟩, ⟨true,1,0x543210dcba987⟩,
  ⟨true,3,0xdcba985432106⟩, ⟨true,3,0xdcba975432106⟩, ⟨true,3,0xdcba875432106⟩,
  ⟨true,3,0xdcb9875432106⟩, ⟨true,3,0xdca9875432106⟩, ⟨true,3,0xdba9875432106⟩,
  ⟨true,0,0x54321cba98706⟩, ⟨true,10,0x54321dcba9876⟩, ⟨true,10,0x54320dcba9876⟩,
  ⟨true,10,0x54310dcba9876⟩, ⟨true,10,0x54210dcba9876⟩, ⟨true,10,0x53210dcba9876⟩,
  ⟨true,10,0x43210dcba9876⟩, ⟨true,1,0x543210dcba987⟩, ⟨true,5,0xdc543210ba986⟩,
  ⟨true,5,0xdc543210ba976⟩, ⟨true,5,0xdc543210ba876⟩, ⟨true,5,0xdc543210b9876⟩,
  ⟨true,5,0xdc543210a9876⟩, ⟨true,3,0xdba9875432106⟩, ⟨true,3,0xcba9875432106⟩,
  ⟨true,11,0x54321dcba9876⟩, ⟨true,11,0x54320dcba9876⟩, ⟨true,11,0x54310dcba9876⟩,
  ⟨true,11,0x54210dcba9876⟩, ⟨true,11,0x53210dcba9876⟩, ⟨true,11,0x43210dcba9876⟩,
  ⟨true,1,0x543210dcba987⟩, ⟨true,7,0xdcb543210a986⟩, ⟨true,7,0xdcb543210a976⟩,
  ⟨true,7,0xdcb543210a876⟩, ⟨true,7,0xdcb5432109876⟩, ⟨true,5,0xdc543210a9876⟩,
  ⟨true,5,0xdb543210a9876⟩, ⟨true,5,0xcb543210a9876⟩, ⟨false,1,0xca8642db97531⟩,
  ⟨false,1,0xdb9753ca86420⟩, ⟨false,1,0xca8640db97531⟩, ⟨false,1,0xdb9751ca86420⟩,
  ⟨false,1,0xca8620db97531⟩, ⟨false,1,0xdb9731ca86420⟩, ⟨false,1,0xca8420db97531⟩,
  ⟨false,1,0xdb9531ca86420⟩, ⟨false,1,0xca6420db97531⟩, ⟨false,1,0xdb7531ca86420⟩,
  ⟨false,1,0xc86420db97531⟩, ⟨false,1,0xd97531ca86420⟩, ⟨false,1,0xa86420db97531⟩,
  ⟨false,1,0xb97531ca86420⟩, ⟨false,1,0xca8642db97531⟩, ⟨false,12,0xb9753ca8642d0⟩,
  ⟨false,12,0xca864b975310d⟩, ⟨false,12,0xb9751ca8642d0⟩, ⟨false,12,0xca862b975310d⟩,
  ⟨false,12,0xb9731ca8642d0⟩, ⟨false,12,0xca842b975310d⟩, ⟨false,12,0xb9531ca8642d0⟩,
  ⟨false,12,0xca642b975310d⟩, ⟨false,12,0xb7531ca8642d0⟩, ⟨false,12,0xc8642b975310d⟩,
  ⟨false,12,0x97531ca8642d0⟩, ⟨false,12,0xa8642b975310d⟩, ⟨false,1,0xb97531ca86420⟩,
  ⟨false,1,0xb97531dca8642⟩, ⟨false,13,0xb9753dca86420⟩, ⟨false,1,0xb97531dca8640⟩,
  ⟨false,13,0xb9751dca86420⟩, ⟨false,1,0xb97531dca8620⟩, ⟨false,13,0xb9731dca86420⟩,
  ⟨false,1,0xb97531dca8420⟩, ⟨false,13,0xb9531dca86420⟩, ⟨false,1,0xb97531dca6420⟩,
  ⟨false,13,0xb7531dca86420⟩, ⟨false,1,0xb97531dc86420⟩, ⟨false,13,0x97531dca86420⟩,
  ⟨false,1,0xb97531da86420⟩, ⟨false,1,0xb97531ca86420⟩, ⟨false,12,0xca864b975312d⟩,
  ⟨false,14,0xb9753ca86420d⟩, ⟨false,12,0xca864b975310d⟩, ⟨false,14,0xb9751ca86420d⟩,
  ⟨false,15,0xca86b9753120d⟩, ⟨false,14,0xb9731ca86420d⟩, ⟨false,15,0xca84b9753120d⟩,
  ⟨false,14,0xb9531ca86420d⟩, ⟨false,15,0xca64b9753120d⟩, ⟨false,14,0xb7531ca86420d⟩,
  ⟨false,15,0xc864b9753120d⟩, ⟨false,14,0x97531ca86420d⟩, ⟨false,15,0xa864b9753120d⟩,
  ⟨false,1,0xb97531ca86420⟩, ⟨false,12,0xb9753ca86421d⟩, ⟨false,13,0xb9753dca86420⟩,
  ⟨false,12,0xb9753ca86401d⟩, ⟨false,16,0xb9751ca86420d⟩, ⟨false,12,0xb9753ca86201d⟩,
  ⟨false,16,0xb9731ca86420d⟩, ⟨false,12,0xb9753ca84201d⟩, ⟨false,16,0xb9531ca86420d⟩,
  ⟨false,12,0xb9753ca64201d⟩, ⟨false,16,0xb7531ca86420d⟩, ⟨false,12,0xb9753c864201d⟩,
  ⟨false,16,0x97531ca86420d⟩, ⟨false,12,0xb9753a864201d⟩, ⟨false,1,0xb97531ca86420⟩,
  ⟨false,15,0xca86b9753142d⟩, ⟨false,17,0xb9753ca86420d⟩, ⟨false,15,0xca86b9753140d⟩,
  ⟨false,17,0xb9751ca86420d⟩, ⟨false,15,0xca86b9753120d⟩, ⟨false,17,0xb9731ca86420d⟩,
  ⟨false,7,0xca8b97531420d⟩, ⟨false,17,0xb9531ca86420d⟩, ⟨false,7,0xca6b97531420d⟩,
  ⟨false,17,0xb7531ca86420d⟩, ⟨false,7,0xc86b97531420d⟩, ⟨false,17,0x97531ca86420d⟩,
  ⟨false,7,0xa86b97531420d⟩, ⟨false,1,0xb97531ca86420⟩, ⟨false,15,0xb975ca864231d⟩,
  ⟨false,16,0xb9753ca86420d⟩, ⟨false,15,0xb975ca864031d⟩, ⟨false,16,0xb9751ca86420d⟩,
  ⟨false,15,0xb975ca862031d⟩, ⟨false,8,0xb9731ca86420d⟩, ⟨false,15,0xb975ca842031d⟩,
  ⟨false,8,0xb9531ca86420d⟩, ⟨false,15,0xb975ca642031d⟩, ⟨false,8,0xb7531ca86420d⟩,
  ⟨false,15,0xb975c8642031d⟩, ⟨false,8,0x97531ca86420d⟩, ⟨false,15,0xb975a8642031d⟩,
  ⟨false,1,0xb97531ca86420⟩]

private def trim (t mark : Fin 14) : Relabel 18 := trims[t.val*14 + mark.val]'(by omega)

private theorem trims_ok : ∀ t mark : Fin 14,
    let w := trim t mark
    (∀ i j : Fin 13, label w i = label w j → i=j) ∧ (∀ i : Fin 13, label w i ≠ mark) ∧
    ∀ i j : Fin 13, i ≠ j → Cert16.edge (core14 t) (label w i).val (label w j).val =
      (if w.flip then !(Cert16.edge (core13 w.shape) i.val j.val) else Cert16.edge (core13 w.shape) i.val j.val) := by
  decide +kernel

theorem trim14 (t mark : Fin 14) :
    ∃ (q : Fin 18) (flip : Bool) (u : Fin 13 → Fin 14),
      (∀ ⦃i j⦄, u i=u j → i=j) ∧ (∀ i, u i ≠ mark) ∧
      ∀ i j, i ≠ j → Cert16.edge (core14 t) (u i).val (u j).val =
        (if flip then !(Cert16.edge (core13 q) i.val j.val) else Cert16.edge (core13 q) i.val j.val) := by
  obtain ⟨inj,missing,edges⟩ := trims_ok t mark
  exact ⟨(trim t mark).shape,(trim t mark).flip,label (trim t mark),fun {_ _} e => inj _ _ e,missing,edges⟩

end Ramsey556.Split17
