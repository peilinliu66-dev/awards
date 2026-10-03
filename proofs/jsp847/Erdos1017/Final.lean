import Erdos1017.FinalPreparations
import Erdos1017.Repacking

/-!
# Uniform dense clique-partition saving

For every finite simple graph, the final endpoint has no seed, low-weight
partition, stability, matching, or asymptotic-threshold hypothesis.
All source is UNCOMPILED. These are proposed proof bodies, not verified results.
-/

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edge_surplus_le_of_small_deficit [Nonempty V] (G : SimpleGraph V)
    (hsmall : 10000 * partitionDeficit G ≤ (Fintype.card V : ℝ)^2) :
    (edgeCount G : ℝ) - (Fintype.card V : ℝ)^2 / 4 ≤ 72 * partitionDeficit G := by
  classical
  obtain ⟨D, hside⟩ := exists_oriented_denseCut G
  have hn : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hcards : (D.left.card : ℝ) + D.leftᶜ.card = Fintype.card V := by
    exact_mod_cast Finset.card_add_card_compl D.left
  obtain ⟨hxR, hyR, hbalance⟩ :=
    balanced_parts_positive hn hcards D.balance_sq_le hsmall
  have hx : 0 < D.left.card := by exact_mod_cast hxR
  have hy : 0 < D.leftᶜ.card := by exact_mod_cast hyR
  obtain ⟨ell, Q, hbudget, hQ⟩ :=
    exists_repacked_partition G D.left hx hy D.rightPartition
  have hbudgetR : (D.left.card : ℝ) * ell ≤
      ((D.left.card : ℝ) - min (D.left.card : ℝ) (D.leftᶜ.card : ℝ)) *
        edgeCount (onVertices G D.left) := by
    have hcast : (D.left.card : ℝ) * ell ≤
        ((D.left.card - min D.left.card D.leftᶜ.card : ℕ) : ℝ) *
          edgeCount (onVertices G D.left) := by exact_mod_cast hbudget
    rw [Nat.cast_sub (min_le_left D.left.card D.leftᶜ.card)] at hcast
    simpa using hcast
  have hell : 9 * (ell : ℝ) ≤ edgeCount (onVertices G D.left) :=
    discarded_le_ninth hxR (Nat.cast_nonneg _) (Nat.cast_nonneg _) hbalance hbudgetR
  have hQreal : (Q.count : ℝ) + edgeCount (onVertices G D.left) ≤
      incidenceCount G D.left D.leftᶜ + 2 * (ell : ℝ) +
        2 * missingCount G D.left D.leftᶜ + D.rightPartition.count := by
    exact_mod_cast hQ
  have hpQ : (partitionNumber G : ℝ) ≤ Q.count := by exact_mod_cast partitionNumber_le Q
  have hpacking : (partitionNumber G : ℝ) + edgeCount (onVertices G D.left) ≤
      incidenceCount G D.left D.leftᶜ + 2 * (ell : ℝ) +
        2 * missingCount G D.left D.leftᶜ + D.rightPartition.count := by linarith
  have hsideR : (edgeCount (onVertices G D.leftᶜ) : ℝ) ≤
      edgeCount (onVertices G D.left) := by exact_mod_cast hside
  have hcutR : (edgeCount G : ℝ) = edgeCount (onVertices G D.left) +
      edgeCount (onVertices G D.leftᶜ) + incidenceCount G D.left D.leftᶜ := by
    exact_mod_cast edgeCount_cut G D.left
  have hedges : (edgeCount G : ℝ) ≤ incidenceCount G D.left D.leftᶜ +
      2 * edgeCount (onVertices G D.left) := by linarith
  exact near_dense_surplus D.deficit_nonneg
    (by unfold partitionDeficit; ring) hpacking (incidenceCount_cut_le G D.left)
    D.missing_le D.right_count_le hell hedges

theorem real_dense_saving [Nonempty V] (G : SimpleGraph V) :
    (edgeCount G : ℝ) - (Fintype.card V : ℝ)^2 / 4 ≤
      2500 * ((Fintype.card V : ℝ)^2 / 4 - partitionNumber G) := by
  have hp : (partitionNumber G : ℝ) ≤ (Fintype.card V : ℝ)^2 / 4 := by
    have hpA : (partitionNumber G : ℝ) ≤ balancedThreshold (Fintype.card V) := by
      exact_mod_cast partitionNumber_le_balancedThreshold G
    exact hpA.trans (square_quarter_floor_bounds (Fintype.card V)).1
  apply uniform_real_saving (Nat.cast_nonneg _) hp (edgeCount_le_half_square G)
  intro hsmall
  exact edge_surplus_le_of_small_deficit G hsmall

/-- The fixed all-order, all-density integer endpoint. -/
theorem uniform_integer_dense_saving (G : SimpleGraph V) :
    5000 * partitionNumber G + edgeCount G ≤
      5001 * balancedThreshold (Fintype.card V) := by
  classical
  by_cases hn : Fintype.card V = 0
  · have hp := partitionNumber_le_balancedThreshold G
    have he := edgeCount_le_half_square G
    have hezero : edgeCount G = 0 := by
      simp only [hn, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div] at he
      have hnat : edgeCount G ≤ 0 := by exact_mod_cast he
      omega
    simp only [hn, balancedThreshold, zero_pow (by decide : 2 ≠ 0), Nat.zero_div] at hp ⊢
    omega
  · letI : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    exact integer_saving_of_real (partitionNumber_le_balancedThreshold G)
      (partitionNumber_lt_balanced_of_dense G) (real_dense_saving G)

/-- An actual exact clique partition realizes the uniform bound. -/
theorem exists_partition_dense_saving (G : SimpleGraph V) :
    ∃ P : CliquePartition G,
      5000 * P.count + edgeCount G ≤
        5001 * balancedThreshold (Fintype.card V) := by
  obtain ⟨P, hP⟩ := exists_minimum_count G
  refine ⟨P, ?_⟩
  rw [hP]
  exact uniform_integer_dense_saving G

/-- No special vertex labeling or parity is assumed in the target statement. -/
theorem denseSavingStatement : DenseSavingStatement (V := V) :=
  uniform_integer_dense_saving

end Erdos1017
