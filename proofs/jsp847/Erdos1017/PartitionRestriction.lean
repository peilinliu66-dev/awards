/-
Copyright (c) 2026. Released under the Apache License 2.0.
Exact partition restriction and counting. UNCOMPILED.
-/
import Erdos1017.GraphCut
import Erdos1017.PartitionExistence

namespace Erdos1017

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace CliquePartition

variable {G : SimpleGraph V}

/-- Restrict each block and discard intersections carrying no edge. -/
noncomputable def restrict (P : CliquePartition G) (S : Finset V) :
    CliquePartition (onVertices G S) := by
  classical
  let T := P.blocks.filter (fun C => 2 ≤ (C ∩ S).card)
  refine ⟨T.image (fun C => C ∩ S), ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact (Finset.mem_filter.mp hD).2
  · intro C hC u hu v hv huv
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨P.clique D (Finset.mem_filter.mp hD).1
      u (Finset.mem_inter.mp hu).1 v (Finset.mem_inter.mp hv).1 huv,
      (Finset.mem_inter.mp hu).2, (Finset.mem_inter.mp hv).2⟩
  · intro u v huv
    obtain ⟨D, hD, huniq⟩ := P.owns u v huv.1
    have hu : u ∈ D ∩ S := Finset.mem_inter.mpr ⟨hD.2.1, huv.2.1⟩
    have hv : v ∈ D ∩ S := Finset.mem_inter.mpr ⟨hD.2.2, huv.2.2⟩
    have hne : u ≠ v := huv.1.ne
    have hsub : ({u, v} : Finset V) ⊆ D ∩ S := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hu, hv⟩
    have hsize : 2 ≤ (D ∩ S).card := by
      simpa [hne] using Finset.card_le_card hsub
    refine ⟨D ∩ S, ⟨Finset.mem_image.mpr
      ⟨D, Finset.mem_filter.mpr ⟨hD.1, hsize⟩, rfl⟩, hu, hv⟩, ?_⟩
    intro C hC
    obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hC.1
    have hEq : E = D := huniq E ⟨(Finset.mem_filter.mp hE).1,
      (Finset.mem_inter.mp hC.2.1).1, (Finset.mem_inter.mp hC.2.2).1⟩
    rw [hEq]

theorem restrict_count_le (P : CliquePartition G) (S : Finset V) :
    (P.restrict S).count ≤
      (P.blocks.filter (fun C => 2 ≤ (C ∩ S).card)).card := by
  classical
  exact Finset.card_image_le

/-- Blocks of order at least three. -/
noncomputable def largeBlocks (P : CliquePartition G) : Finset (Finset V) := by
  classical
  exact P.blocks.filter (fun C => 3 ≤ C.card)

/-- Two-vertex blocks fully contained in a set. -/
noncomputable def pairBlocksOn (P : CliquePartition G) (S : Finset V) :
    Finset (Finset V) := by
  classical
  exact P.blocks.filter (fun C => C.card = 2 ∧ C ⊆ S)

theorem restrict_count_le_large_add_pairs (P : CliquePartition G) (S : Finset V) :
    (P.restrict S).count ≤ P.largeBlocks.card + (P.pairBlocksOn S).card := by
  classical
  have hsub : P.blocks.filter (fun C => 2 ≤ (C ∩ S).card) ⊆
      P.largeBlocks ∪ P.pairBlocksOn S := by
    intro C hC
    obtain ⟨hCP, hsize⟩ := Finset.mem_filter.mp hC
    have hlarge := P.nontrivial C hCP
    by_cases htwo : C.card = 2
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨hCP, htwo, ?_⟩
      have hEq : C ∩ S = C := Finset.eq_of_subset_of_card_le
        Finset.inter_subset_left (by omega)
      intro u hu
      have : u ∈ C ∩ S := by rwa [hEq]
      exact (Finset.mem_inter.mp this).2
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hCP, by omega⟩
  exact (P.restrict_count_le S).trans
    ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))

theorem two_count_add_large_le_weight (P : CliquePartition G) :
    2 * P.count + P.largeBlocks.card ≤ P.weight := by
  classical
  have h : (∑ C ∈ P.blocks, (2 + if 3 ≤ C.card then 1 else 0)) ≤
      ∑ C ∈ P.blocks, C.card := by
    apply Finset.sum_le_sum
    intro C hC
    have hn := P.nontrivial C hC
    split_ifs <;> omega
  simpa only [count, weight, largeBlocks, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_filter, Nat.nsmul_eq_mul, Nat.mul_comm] using h

/-- The graph of the two-vertex pieces of a partition. -/
def skeleton (P : CliquePartition G) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ({u, v} : Finset V) ∈ P.blocks
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem skeleton_le (P : CliquePartition G) : P.skeleton ≤ G := by
  intro u v h
  exact P.clique {u, v} h.2 u (by simp) v (by simp) h.1

private theorem sym2_toFinset_injective :
    Function.Injective (Sym2.toFinset : Sym2 V → Finset V) := by
  intro e f h
  apply Sym2.ext
  intro v
  simpa using (show v ∈ e.toFinset ↔ v ∈ f.toFinset by rw [h])

/-- A literal bijection between skeleton edges in `S` and original pair blocks. -/
theorem pairBlocksOn_card (P : CliquePartition G) (S : Finset V) :
    (P.pairBlocksOn S).card = edgeCount (onVertices P.skeleton S) := by
  classical
  have hset : P.pairBlocksOn S =
      (onVertices P.skeleton S).edgeFinset.image Sym2.toFinset := by
    ext C
    constructor
    · intro hC
      obtain ⟨hCP, htwo, hCS⟩ := Finset.mem_filter.mp hC
      obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp htwo
      refine Finset.mem_image.mpr ⟨s(u, v), ?_, ?_⟩
      · have hu : u ∈ S := hCS (by simp)
        have hv : v ∈ S := hCS (by simp)
        apply SimpleGraph.mem_edgeFinset.mpr
        exact ⟨⟨huv, hCP⟩, hu, hv⟩
      · exact Sym2.toFinset_mk_eq
    · intro hC
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hC
      revert he
      refine Sym2.ind (fun u v he => ?_) e
      have h : (u ≠ v ∧ ({u, v} : Finset V) ∈ P.blocks) ∧ u ∈ S ∧ v ∈ S :=
        SimpleGraph.mem_edgeFinset.mp he
      rw [Sym2.toFinset_mk_eq]
      apply Finset.mem_filter.mpr
      refine ⟨h.1.2, by simp [h.1.1], ?_⟩
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨h.2.1, h.2.2⟩
  rw [hset, Finset.card_image_of_injective _ sym2_toFinset_injective]
  rfl

theorem restrict_count_le_large_add_internal (P : CliquePartition G) (S : Finset V) :
    (P.restrict S).count ≤ P.largeBlocks.card +
      edgeCount (onVertices P.skeleton S) := by
  simpa only [P.pairBlocksOn_card S] using P.restrict_count_le_large_add_pairs S

end CliquePartition

end Erdos1017
