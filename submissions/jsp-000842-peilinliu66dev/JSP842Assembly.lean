import JSP842DenseSubset
import JSP842ThresholdBound
import JSP842CycleBridge
import JSP842Maximal

namespace JSP842

/-- Explicit interface for the separately proved finite Ore edge-addition lemma. -/
def OreClosureStatement (V : Type) [Fintype V] [DecidableEq V] : Prop :=
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V),
    3 ≤ Fintype.card V → u ≠ v → ¬G.Adj u v →
    Fintype.card V ≤ G.degree u + G.degree v →
    (G ⊔ SimpleGraph.edge u v).IsHamiltonian → G.IsHamiltonian

/-- Internal assembly. The exported unconditional endpoint must instantiate `hOre`
with the proved Ore theorem; this helper by itself is not a solution. -/
theorem threshold_of_ore_closure
    (hOre : ∀ (V : Type) [Fintype V] [DecidableEq V], OreClosureStatement V)
    (k n : ℕ) (hn : 5 * k + 5 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (he : (n - k - 1).choose 2 + (k + 2).choose 2 + 1 ≤ G.edgeFinset.card) :
    ∃ v : Fin n, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = n - k := by
  classical
  have hkn : k ≤ n := by omega
  have hm : 4 * k + 5 ≤ n - k := by omega
  obtain ⟨s, hs, hb⟩ := exists_dense_induced_subset G (n - k) (by omega) (by simp)
  let H : SimpleGraph (↑s : Set (Fin n)) := G.induce (↑s : Set (Fin n))
  have hcard : Fintype.card (↑s : Set (Fin n)) = n - k := by simpa using hs
  have hmH : 4 * k + 5 ≤ Fintype.card (↑s : Set (Fin n)) := by omega
  have hm3 : 3 ≤ Fintype.card (↑s : Set (Fin n)) := by omega
  have hb' : G.edgeFinset.card ≤ H.edgeFinset.card + k * H.minDegree + (k + 1).choose 2 := by
    simpa only [H, Fintype.card_fin, show n - (n - k) = k by omega] using hb
  have hHam : H.IsHamiltonian := by
    by_contra hN
    obtain ⟨F, hHF, hFN, hmax⟩ := maximal_nonhamiltonian_supergraph H hN
    have hne : F ≠ ⊤ := by
      intro hF
      apply hFN
      rw [hF]
      exact top_isHamiltonian hm3
    have hc : ∀ u v, u ≠ v → ¬F.Adj u v →
        F.degree u + F.degree v ≤ Fintype.card (↑s : Set (Fin n)) - 1 := by
      intro u v huv hnot
      by_contra hdeg
      have hsum : Fintype.card (↑s : Set (Fin n)) ≤ F.degree u + F.degree v := by omega
      have hlt : F < F ⊔ SimpleGraph.edge u v := SimpleGraph.lt_sup_edge F u v huv hnot
      exact hFN (hOre _ F u v hm3 huv hnot hsum (hmax _ hlt))
    have hupper := closed_supergraph_threshold_bound H F k hmH hHF hne hc
    rw [hcard] at hupper
    omega
  obtain ⟨v, p, hp, hlen⟩ := cycle_of_induce_isHamiltonian G s (by omega) hHam
  exact ⟨v, p, hp, hlen.trans hs⟩

#print axioms threshold_of_ore_closure
end JSP842
