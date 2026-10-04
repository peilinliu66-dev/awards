import Erdos524.GaussianBoxDensity
import Erdos524.GaussianCovarianceComparison
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! Invertible covariance square-root coordinates, determinant and quadratic energy. -/

namespace Erdos524.GaussianCovarianceCoordinates

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
open Erdos524.GaussianBoxDensity Erdos524.GaussianLevelSets
open Erdos524.GaussianCovarianceComparison

variable {n : ℕ}

noncomputable def matrixEquiv (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.det ≠ 0) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  (A.toLinearEquiv' (Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA))).toContinuousLinearEquiv

theorem matrixEquiv_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.det ≠ 0)
    (x : Fin (n + 1) → ℝ) : matrixEquiv A hA x = A *ᵥ x := rfl

theorem matrixEquiv_symm_apply (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.det ≠ 0)
    (x : Fin (n + 1) → ℝ) : (matrixEquiv A hA).symm x = A⁻¹ *ᵥ x := rfl

theorem inverseJacobian_matrixEquiv (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.det ≠ 0) : inverseJacobian (matrixEquiv A hA) = ENNReal.ofReal (|A.det|⁻¹) := by
  have he : ((matrixEquiv A hA).symm : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ)) =
      Matrix.toLin' A⁻¹ := by ext x; rfl
  unfold inverseJacobian
  rw [he, LinearMap.det_toLin', Matrix.det_nonsing_inv, Ring.inverse_eq_inv, abs_inv]

theorem sqrt_det_eq (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : S.PosSemidef) :
    (CFC.sqrt S).det = Real.sqrt S.det := by
  simpa using hS.det_sqrt

theorem sqrt_det_ne_zero (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : S.PosDef) :
    (CFC.sqrt S).det ≠ 0 := by
  rw [sqrt_det_eq S hS.posSemidef]
  exact ne_of_gt (Real.sqrt_pos.mpr hS.det_pos)

noncomputable def sqrtEquiv (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : S.PosDef) :
    (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
  matrixEquiv (CFC.sqrt S) (sqrt_det_ne_zero S hS)

theorem inverseJacobian_sqrtEquiv (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hS : S.PosDef) : inverseJacobian (sqrtEquiv S hS) = ENNReal.ofReal (1 / Real.sqrt S.det) := by
  rw [sqrtEquiv, inverseJacobian_matrixEquiv, sqrt_det_eq S hS.posSemidef,
    abs_of_nonneg (Real.sqrt_nonneg _), one_div]

theorem energy_mulVec (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (x : Fin (n + 1) → ℝ) :
    energy (A *ᵥ x) = x ⬝ᵥ (Aᵀ * A) *ᵥ x := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  simp [energy, dotProduct, pow_two]

theorem energy_inverse_sqrt (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hS : S.PosDef) (x : Fin (n + 1) → ℝ) :
    energy ((sqrtEquiv S hS).symm x) = x ⬝ᵥ S⁻¹ *ᵥ x := by
  have hsym : (CFC.sqrt S)ᵀ = CFC.sqrt S :=
    (CFC.sqrt_nonneg S).posSemidef.isHermitian.isSymm
  rw [sqrtEquiv, matrixEquiv_symm_apply, energy_mulVec,
    Matrix.transpose_nonsing_inv, hsym, ← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]

theorem map_pi_sqrtEquiv (S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hS : S.PosDef) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map (sqrtEquiv S hS) =
      (multivariateGaussian 0 S).map ofLp := by
  rw [multivariate_zero_eq_map_pi, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

theorem quadratic_le_card_mul_diagonal_sum
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosSemidef)
    (x : Fin (n + 1) → ℝ) :
    x ⬝ᵥ S *ᵥ x ≤ (n + 1 : ℝ) * ∑ j, (x j) ^ 2 * S j j := by
  let A := CFC.sqrt S
  have hsym : Aᵀ = A := (CFC.sqrt_nonneg S).posSemidef.isHermitian.isSymm
  have hAA : Aᵀ * A = S := by rw [hsym]; exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  have he : x ⬝ᵥ S *ᵥ x = energy (A *ᵥ x) := by rw [energy_mulVec, hAA]
  rw [he]
  have hrow (i : Fin (n + 1)) :
      (∑ j, A i j * x j) ^ 2 ≤ (n + 1 : ℝ) * ∑ j, (A i j * x j) ^ 2 := by
    simpa [mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A i j * x j) (fun _ ↦ (1 : ℝ))
  calc
    energy (A *ᵥ x) = ∑ i, (∑ j, A i j * x j) ^ 2 := rfl
    _ ≤ ∑ i, (n + 1 : ℝ) * ∑ j, (A i j * x j) ^ 2 :=
      Finset.sum_le_sum fun i _ ↦ hrow i
    _ = (n + 1 : ℝ) * ∑ j, (x j) ^ 2 * ∑ i, (A i j) ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hd : (∑ i, (A i j) ^ 2) = S j j := by
        have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ ↦ M j j) hAA
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using h
      rw [hd]

end Erdos524.GaussianCovarianceCoordinates
