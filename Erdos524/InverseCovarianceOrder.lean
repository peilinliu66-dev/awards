import Erdos524.FiniteKernelPerturbation

/-! Inverse covariance order from two finite Schur complements over the real field. -/

namespace Erdos524.InverseCovarianceOrder

open Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

variable {n : ℕ}

theorem posDef_of_gap {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : B.PosDef := by
  have h := hA.add_posSemidef hBA
  have he : A + (B - A) = B := by abel
  rwa [he] at h

theorem inverse_antitone {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (hBA : (B - A).PosSemidef) : (A⁻¹ - B⁻¹).PosSemidef := by
  have hB := posDef_of_gap hA hBA
  letI := invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
  letI := invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB.det_pos.ne')
  letI := invertibleOfIsUnitDet A⁻¹ (isUnit_iff_ne_zero.mpr hA.inv.det_pos.ne')
  have hblock : (fromBlocks B (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)ᴴ A⁻¹).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₂₂ B (1 : Matrix (Fin n) (Fin n) ℝ) hA.inv).mpr
    simpa only [conjTranspose_one, one_mul, mul_one, inv_inv_of_invertible] using hBA
  have h := (Matrix.PosDef.fromBlocks₁₁ (1 : Matrix (Fin n) (Fin n) ℝ) A⁻¹ hB).mp hblock
  simpa only [conjTranspose_one, one_mul, mul_one] using h

theorem half_gap_inverse {C A : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.PosDef) (hgap : (A - (1 / 2 : ℝ) • C).PosSemidef) :
    A.PosDef ∧ ((2 : ℝ) • C⁻¹ - A⁻¹).PosSemidef := by
  have hhalf := hC.smul (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨posDef_of_gap hhalf hgap, ?_⟩
  have h := inverse_antitone hhalf hgap
  letI := invertibleOfNonzero (by norm_num : (1 / 2 : ℝ) ≠ 0)
  rw [Matrix.inv_smul C (1 / 2 : ℝ) (isUnit_iff_ne_zero.mpr hC.det_pos.ne')] at h
  norm_num [invOf_eq_inv] at h
  exact h

theorem half_gap_inverse_diagonal {C A : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.PosDef) (hgap : (A - (1 / 2 : ℝ) • C).PosSemidef) (i : Fin n) :
    A⁻¹ i i ≤ 2 * C⁻¹ i i := by
  have h := (half_gap_inverse hC hgap).2.diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] using sub_nonneg.mp h

end Erdos524.InverseCovarianceOrder
