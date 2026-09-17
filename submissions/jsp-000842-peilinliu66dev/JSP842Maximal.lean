import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Order.Preorder.Finite

namespace JSP842

/-- Every finite non-Hamiltonian graph is contained in a maximal non-Hamiltonian graph. -/
theorem maximal_nonhamiltonian_supergraph {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬G.IsHamiltonian) :
    ∃ H : SimpleGraph V, G ≤ H ∧ ¬H.IsHamiltonian ∧
      ∀ K : SimpleGraph V, H < K → K.IsHamiltonian := by
  classical
  obtain ⟨H, hGH, hH⟩ :=
    Finite.exists_le_maximal (p := fun K : SimpleGraph V => ¬K.IsHamiltonian) hG
  refine ⟨H, hGH, hH.prop, ?_⟩
  intro K hHK
  by_contra hK
  exact (not_le_of_gt hHK) (hH.2 hK hHK.le)

end JSP842

#print axioms JSP842.maximal_nonhamiltonian_supergraph
