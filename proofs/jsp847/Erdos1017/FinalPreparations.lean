import Erdos1017.NumericalSaving

/-! Unconditional cut supply and orientation of its denser internal side.
Original source implementation. UNCOMPILED. -/

namespace Erdos1017

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_denseCut [Nonempty V] (G : SimpleGraph V) : Nonempty (DenseCut G) := by
  apply exists_denseCut_of_weighted_partition G
  obtain ⟨P, hP⟩ := exists_weighted_partition G
  refine ⟨P, ?_⟩
  have hPR : (P.weight : ℝ) ≤ 2 * (balancedThreshold (Fintype.card V) : ℝ) := by
    exact_mod_cast hP
  have hfloor := (square_quarter_floor_bounds (Fintype.card V)).1
  linarith

theorem missingCount_symm (G : SimpleGraph V) (A B : Finset V) :
    missingCount G A B = missingCount G B A := by
  have hAB := incidenceCount_add_missing G A B
  have hBA := incidenceCount_add_missing G B A
  rw [incidenceCount_symm G B A, Nat.mul_comm] at hBA
  omega

namespace DenseCut

variable {G : SimpleGraph V}

noncomputable def swap (D : DenseCut G) : DenseCut G where
  left := D.leftᶜ
  leftPartition := D.rightPartition
  rightPartition := {
    blocks := D.leftPartition.blocks
    nontrivial := D.leftPartition.nontrivial
    clique := by simpa only [compl_compl] using D.leftPartition.clique
    owns := by simpa only [compl_compl] using D.leftPartition.owns }
  deficit_nonneg := D.deficit_nonneg
  missing_le := by
    simpa only [compl_compl, missingCount_symm G D.leftᶜ D.left] using D.missing_le
  balance_sq_le := by
    have hcard : (D.left.card : ℝ) + D.leftᶜ.card = Fintype.card V := by
      exact_mod_cast Finset.card_add_card_compl D.left
    have heq : ((D.leftᶜ.card : ℝ) - (Fintype.card V : ℝ) / 2)^2 =
        ((D.left.card : ℝ) - (Fintype.card V : ℝ) / 2)^2 := by
      have hcompl : (D.leftᶜ.card : ℝ) = (Fintype.card V : ℝ) - D.left.card := by linarith
      rw [hcompl]
      ring
    rw [heq]
    exact D.balance_sq_le
  left_count_le := D.right_count_le
  right_count_le := D.left_count_le

end DenseCut

theorem exists_oriented_denseCut [Nonempty V] (G : SimpleGraph V) :
    ∃ D : DenseCut G,
      edgeCount (onVertices G D.leftᶜ) ≤ edgeCount (onVertices G D.left) := by
  obtain ⟨D⟩ := exists_denseCut G
  by_cases h : edgeCount (onVertices G D.leftᶜ) ≤ edgeCount (onVertices G D.left)
  · exact ⟨D, h⟩
  · exact ⟨D.swap, by simpa [DenseCut.swap] using le_of_lt (lt_of_not_ge h)⟩

theorem incidenceCount_cut_le (G : SimpleGraph V) (X : Finset V) :
    (incidenceCount G X Xᶜ : ℝ) ≤ (Fintype.card V : ℝ)^2 / 4 := by
  have hcount := incidenceCount_add_missing G X Xᶜ
  have hcountR : (incidenceCount G X Xᶜ : ℝ) + missingCount G X Xᶜ =
      (X.card : ℝ) * Xᶜ.card := by exact_mod_cast hcount
  have hcards : (X.card : ℝ) + Xᶜ.card = Fintype.card V := by
    exact_mod_cast Finset.card_add_card_compl X
  have hmissing : (0 : ℝ) ≤ missingCount G X Xᶜ := Nat.cast_nonneg _
  rw [← hcards]
  nlinarith [sq_nonneg ((X.card : ℝ) - Xᶜ.card)]

theorem edgeCount_le_half_square (G : SimpleGraph V) :
    (edgeCount G : ℝ) ≤ (Fintype.card V : ℝ)^2 / 2 := by
  have h := incidenceCount_add_missing G Finset.univ Finset.univ
  rw [incidenceCount_univ, Finset.card_univ] at h
  have hle : 2 * edgeCount G ≤ Fintype.card V * Fintype.card V := by omega
  have hR : 2 * (edgeCount G : ℝ) ≤ (Fintype.card V : ℝ) * Fintype.card V := by
    exact_mod_cast hle
  nlinarith

end Erdos1017
