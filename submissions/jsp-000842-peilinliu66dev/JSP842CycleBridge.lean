import Mathlib

namespace JSP842

theorem top_isHamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (hm : 3 ≤ Fintype.card V) : (⊤ : SimpleGraph V).IsHamiltonian := by
  classical
  have hc : SimpleGraph.IsContained (SimpleGraph.cycleGraph (Fintype.card V))
      (⊤ : SimpleGraph V) :=
    SimpleGraph.isContained_top_iff.mpr ⟨(Fintype.equivFin V).symm.toEmbedding⟩
  obtain ⟨v, p, hp, hlen⟩ := (SimpleGraph.cycleGraph_isContained_iff (by omega)).mp hc
  intro _
  exact ⟨v, p, SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr ⟨hp, hlen⟩⟩

theorem cycle_of_induce_isHamiltonian {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) (hs : 3 ≤ s.card)
    (h : (G.induce (↑s : Set V)).IsHamiltonian) :
    ∃ v : V, ∃ p : G.Walk v v, p.IsCycle ∧ p.length = s.card := by
  classical
  have hc : Fintype.card (↑s : Set V) = s.card := by simp
  obtain ⟨v, p, hp⟩ := h (by omega)
  let f : G.induce (↑s : Set V) →g G := (SimpleGraph.Embedding.induce _).toHom
  refine ⟨f v, p.map f, hp.isCycle.map Subtype.val_injective, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  simpa only [hc] using hp.length_eq

#print axioms cycle_of_induce_isHamiltonian
#print axioms top_isHamiltonian
end JSP842
