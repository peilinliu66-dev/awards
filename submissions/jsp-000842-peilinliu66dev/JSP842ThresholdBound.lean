import JSP842Arithmetic
import JSP842ClosedBound

namespace JSP842

/-- The quantitative contradiction used after passing to a maximal non-Hamiltonian
supergraph. All graph and counting hypotheses are explicit here. -/
theorem closed_supergraph_threshold_bound {V : Type*} [Fintype V] [DecidableEq V]
    (H F : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel F.Adj]
    (k : ℕ) (hm : 4 * k + 5 ≤ Fintype.card V) (hHF : H ≤ F)
    (hne : F ≠ ⊤)
    (hclosed : ∀ u v, u ≠ v → ¬F.Adj u v →
      F.degree u + F.degree v ≤ Fintype.card V - 1) :
    H.edgeFinset.card + k * H.minDegree + (k + 1).choose 2 ≤
      (Fintype.card V - 1).choose 2 + (k + 2).choose 2 := by
  have he : H.edgeFinset.card ≤ F.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hHF)
  have hd : H.minDegree ≤ F.minDegree :=
    SimpleGraph.Hom.minDegree_mono (f := SimpleGraph.Hom.ofLE hHF) Function.bijective_id
  rcases closedGraph_edge_bound F (by omega) hne hclosed with hz | ⟨t, ht, htm, hdt, het⟩
  · have hHz : H.minDegree = 0 := by omega
    rw [hHz, mul_zero, add_zero]
    exact (Nat.add_le_add_right (he.trans hz.2) _).trans
      (isolated_bound_le_threshold (Fintype.card V) k)
  · have hdp : k * H.minDegree ≤ k * t := Nat.mul_le_mul_left k (hd.trans hdt)
    calc
      H.edgeFinset.card + k * H.minDegree + (k + 1).choose 2 ≤
          (Fintype.card V - t).choose 2 + t * t + k * t + (k + 1).choose 2 := by omega
      _ ≤ _ := closed_bound_le_threshold (Fintype.card V) k t hm ht htm

#print axioms closed_supergraph_threshold_bound
end JSP842
