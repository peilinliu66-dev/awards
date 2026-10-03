/-
Copyright (c) 2026. Released under the Apache License 2.0.
Minimum-weight skeleton and its actual cut partitions. UNCOMPILED.

The finite extraction follows Bo Ning, arXiv:2608.11536v1, Lemmas 4.2--4.4.
The cut estimate is proved in GraphCut by a maximum-degree argument.
-/
import Erdos1017.MinimumSkeleton

namespace Erdos1017

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def partitionDeficit (G : SimpleGraph V) : ℝ :=
  (Fintype.card V : ℝ)^2 / 4 - partitionNumber G

theorem missingCount_antitone {H G : SimpleGraph V} (hHG : H ≤ G)
    (A B : Finset V) : missingCount G A B ≤ missingCount H A B := by
  classical
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  by_cases hH : H.Adj u v
  · have hG := hHG hH
    simp [hH, hG]
  · by_cases hG : G.Adj u v <;> simp [hH, hG]

/-- Every numerical estimate is accompanied by the actual cut and its exact
edge partitions. No packing or cut existence is hidden in a hypothesis. -/
structure DenseCut (G : SimpleGraph V) where
  left : Finset V
  leftPartition : CliquePartition (onVertices G left)
  rightPartition : CliquePartition (onVertices G leftᶜ)
  deficit_nonneg : 0 ≤ partitionDeficit G
  missing_le : (missingCount G left leftᶜ : ℝ) ≤ 6 * partitionDeficit G
  balance_sq_le : ((left.card : ℝ) - (Fintype.card V : ℝ) / 2)^2 ≤
    6 * partitionDeficit G
  left_count_le : (leftPartition.count : ℝ) ≤ 5 * partitionDeficit G
  right_count_le : (rightPartition.count : ℝ) ≤ 5 * partitionDeficit G

/-- The one classical input is an actual low-weight partition. The weighted
foundation theorem supplies it in the final application. All cut, minimum,
restriction, and triangle-free arguments are discharged here. -/
theorem exists_denseCut_of_weighted_partition [Nonempty V] (G : SimpleGraph V)
    (hweighted : ∃ Q : CliquePartition G,
      (Q.weight : ℝ) ≤ (Fintype.card V : ℝ)^2 / 2) :
    Nonempty (DenseCut G) := by
  classical
  obtain ⟨P, hmin⟩ := exists_minimum_weight G
  obtain ⟨Q, hQ⟩ := hweighted
  have hPw : (P.weight : ℝ) ≤ (Fintype.card V : ℝ)^2 / 2 :=
    (show (P.weight : ℝ) ≤ Q.weight by exact_mod_cast hmin Q).trans hQ
  have hpc : (partitionNumber G : ℝ) ≤ P.count := by
    exact_mod_cast partitionNumber_le P
  have hlarge : 2 * (P.count : ℝ) + P.largeBlocks.card ≤ P.weight := by
    exact_mod_cast P.two_count_add_large_le_weight
  have hcount : 2 * (P.count : ℝ) ≤ P.weight := by
    exact_mod_cast P.two_mul_count_le_weight
  have hd : 0 ≤ partitionDeficit G := by
    unfold partitionDeficit
    linarith
  have hr : (P.largeBlocks.card : ℝ) ≤ 2 * partitionDeficit G := by
    unfold partitionDeficit
    linarith
  have hskel : (edgeCount P.skeleton : ℝ) + P.largeBlocks.card = P.count := by
    exact_mod_cast P.skeleton_edges_add_large
  have hdefH : (Fintype.card V : ℝ)^2 / 4 - edgeCount P.skeleton ≤
      3 * partitionDeficit G := by
    unfold partitionDeficit at hr ⊢
    linarith
  obtain ⟨K⟩ := exists_mantelCut P.skeleton (P.skeleton_triangleFree hmin)
  have hleftzero : edgeCount (onVertices P.skeleton K.left) = 0 :=
    edgeCount_onVertices_eq_zero P.skeleton K.left K.independent
  have hleft := P.restrict_count_le_large_add_internal K.left
  rw [hleftzero, Nat.add_zero] at hleft
  have hleftR : ((P.restrict K.left).count : ℝ) ≤ P.largeBlocks.card := by
    exact_mod_cast hleft
  have hrightR : ((P.restrict K.leftᶜ).count : ℝ) ≤
      (P.largeBlocks.card : ℝ) + edgeCount (onVertices P.skeleton K.leftᶜ) := by
    exact_mod_cast P.restrict_count_le_large_add_internal K.leftᶜ
  have hmiss : (missingCount G K.left K.leftᶜ : ℝ) ≤
      missingCount P.skeleton K.left K.leftᶜ := by
    exact_mod_cast missingCount_antitone P.skeleton_le K.left K.leftᶜ
  refine ⟨{
    left := K.left
    leftPartition := P.restrict K.left
    rightPartition := P.restrict K.leftᶜ
    deficit_nonneg := hd
    missing_le := ?_
    balance_sq_le := ?_
    left_count_le := ?_
    right_count_le := ?_ }⟩
  · have h := K.missing_le
    linarith
  · have h := K.balance_sq_le
    linarith
  · linarith
  · have h := K.internal_le
    linarith

end Erdos1017
