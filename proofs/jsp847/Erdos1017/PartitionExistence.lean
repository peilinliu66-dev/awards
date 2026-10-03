import Erdos1017.Definitions

/-! Exact singleton-edge partition and attainment of the two finite minima.
UNCOMPILED source. No graph-theoretic extremal bound is assumed here. -/

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem pair_isClique {G : SimpleGraph V} {u v : V} (huv : G.Adj u v) :
    IsClique G {u, v} := by
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact huv
  · exact huv.symm
  · exact False.elim (hab rfl)

/-- Every edge is itself a block. -/
noncomputable def edgePartition (G : SimpleGraph V) : CliquePartition G := by
  classical
  let S : Finset (Finset V) := Finset.univ.filter
    (fun C => C.card = 2 ∧ IsClique G C)
  refine ⟨S, ?_, ?_, ?_⟩
  · intro C hC
    exact le_of_eq (Finset.mem_filter.mp hC).2.1.symm
  · intro C hC
    exact (Finset.mem_filter.mp hC).2.2
  · intro u v huv
    have hne : u ≠ v := huv.ne
    have hpair : ({u, v} : Finset V).card = 2 := by simp [hne]
    refine ⟨{u, v}, ?_, ?_⟩
    · exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair, pair_isClique huv⟩,
        by simp, by simp⟩
    · intro C hC
      have hcard : C.card = 2 := (Finset.mem_filter.mp hC.1).2.1
      have hsub : ({u, v} : Finset V) ⊆ C := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hC.2.1
        · exact hC.2.2
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem exists_partition (G : SimpleGraph V) : Nonempty (CliquePartition G) :=
  ⟨edgePartition G⟩

theorem exists_minimum_count (G : SimpleGraph V) :
    ∃ P : CliquePartition G, P.count = partitionNumber G := by
  have hs : ({m : ℕ | ∃ P : CliquePartition G, P.count = m} : Set ℕ).Nonempty :=
    ⟨(edgePartition G).count, edgePartition G, rfl⟩
  exact csInf_mem hs

theorem partitionNumber_le {G : SimpleGraph V} (P : CliquePartition G) :
    partitionNumber G ≤ P.count := by
  exact csInf_le (OrderBot.bddBelow _) ⟨P, rfl⟩

theorem exists_minimum_weight (G : SimpleGraph V) :
    ∃ P : CliquePartition G, ∀ Q : CliquePartition G, P.weight ≤ Q.weight := by
  let S : Set ℕ := {m | ∃ P : CliquePartition G, P.weight = m}
  have hs : S.Nonempty := ⟨(edgePartition G).weight, edgePartition G, rfl⟩
  obtain ⟨P, hP⟩ := csInf_mem hs
  refine ⟨P, fun Q => ?_⟩
  rw [hP]
  exact csInf_le (OrderBot.bddBelow _) ⟨Q, rfl⟩

/-- A bound on the minimum is always realized by an actual partition. -/
theorem exists_partition_of_bound {G : SimpleGraph V} {b : ℕ}
    (h : partitionNumber G ≤ b) : ∃ P : CliquePartition G, P.count ≤ b := by
  obtain ⟨P, hP⟩ := exists_minimum_count G
  refine ⟨P, ?_⟩
  rw [hP]
  exact h

end Erdos1017
