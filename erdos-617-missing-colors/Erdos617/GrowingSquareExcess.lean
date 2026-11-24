import Erdos617.TwoLineWitnessCapacity
import Erdos617.RankWitnessRows

namespace Erdos617

open Finset SimpleGraph

/-- On a square outside two full lines, every foreign color that meets all
r-sets and has no r-clique has an edge excess that grows faster than linearly
in r. Otherwise the two outside lines overfill the cleaned rank partition. -/
theorem impossible_small_two_line_good {V : Type*} [Fintype V] [DecidableEq V]
    {r b : ℕ} {c : Sym2 V → Fin r} (large : 4000*(b+1)^2<r) (hb : Balanced c)
    {i j k : Fin r} (ki : k≠i) (kj : k≠j) (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1)
    (cap : rankOn (colorGraph c k) U≤r-1) (no : ∀ S⊆U, ¬(colorGraph c k).IsNClique r S)
    (budget : blockEdges (colorGraph c k) U ≤ (r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) : False := by
  have hr : 6≤r := by nlinarith only [large,Nat.zero_le (b*b),Nat.zero_le b]
  obtain ⟨n,J,P,O,jU,ind,size,small,row,dis,apart,sep,sepJ,score⟩ :=
    clean_rank_witness_rows c k hr hb U sz cap no (b:=b) (by nlinarith only [large]) budget
  have high : 145≤r ∧ 64*(b+1)+4≤r := by constructor <;> nlinarith only [large,Nat.zero_le (b*b),Nat.zero_le b]
  exact two_line_witness_capacity high.1 high.2 hb ki kj C D U J P O fullC fullD meet out jU ind size
    small row dis apart sep sepJ (score.trans (by omega))

/-- On a square outside two full lines, every foreign color that meets all
r-sets and has no r-clique has a quadratic edge excess
above the refined Turán bound. Otherwise the two outside lines overfill the cleaned rank partition. -/
theorem impossible_linear_two_line_good {V : Type*} [Fintype V] [DecidableEq V]
    {r b : ℕ} {c : Sym2 V → Fin r} (hr : 145≤r) (large : 64*(b+1)+4≤r) (hb : Balanced c)
    {i j k : Fin r} (ki : k≠i) (kj : k≠j) (C D U : Finset V)
    (fullC : (colorGraph c i).IsNClique r C) (fullD : (colorGraph c j).IsNClique r D)
    (meet : (C∩D).card=1) (out : Disjoint U (C∪D)) (sz : U.card=(r-1)^2+1)
    (cap : rankOn (colorGraph c k) U≤r-1) (no : ∀ S⊆U, ¬(colorGraph c k).IsNClique r S)
    (budget : blockEdges (colorGraph c k) U ≤ (r-1)*(r-1).choose 2+2*(r-1)-1+b*(r-2)) : False := by
  obtain ⟨n,J,P,O,jU,ind,size,small,row,dis,apart,sep,sepJ,score⟩ :=
    clean_rank_witness_rows_linear c k (by omega) hb U sz cap no (b:=b) (by omega) budget
  exact two_line_witness_capacity hr large hb ki kj C D U J P O fullC fullD meet out jU ind size
    small row dis apart sep sepJ score

end Erdos617
