import Erdos524.GaussianCovarianceCoordinates

/-! Explicit box bounds for actual positive-definite multivariate Gaussian measures. -/

namespace Erdos524.GaussianCovarianceBox

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators
open Erdos524.GaussianBoxDensity Erdos524.GaussianLevelSets
open Erdos524.GaussianCovarianceCoordinates

variable {n : ℕ}

theorem gaussian_box_upper {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) (w : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 S) (ofLp ⁻¹' box w) ≤
      normalization n * ENNReal.ofReal (1 / Real.sqrt S.det) *
        ∏ i, ENNReal.ofReal (2 * w i) := by
  have h := linearEquiv_gaussian_box_upper (sqrtEquiv S hS) w
  rw [map_pi_sqrtEquiv, Measure.map_apply (by fun_prop) (measurableSet_box w),
    inverseJacobian_sqrtEquiv] at h
  exact h

theorem gaussian_box_lower {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) (w : Fin (n + 1) → ℝ) (Q : ℝ)
    (hQ : ∀ y ∈ box w, y ⬝ᵥ S⁻¹ *ᵥ y ≤ Q) :
    normalization n * ENNReal.ofReal (Real.exp (-Q / 2)) *
        ENNReal.ofReal (1 / Real.sqrt S.det) * (∏ i, ENNReal.ofReal (2 * w i)) ≤
      (multivariateGaussian 0 S) (ofLp ⁻¹' box w) := by
  have h := linearEquiv_gaussian_box_lower (sqrtEquiv S hS) w Q (fun y hy ↦ by
    rw [energy_inverse_sqrt]
    exact hQ y hy)
  rw [map_pi_sqrtEquiv, Measure.map_apply (by fun_prop) (measurableSet_box w),
    inverseJacobian_sqrtEquiv] at h
  exact h

theorem quadratic_le_box_diagonal_budget
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosSemidef)
    (w : Fin (n + 1) → ℝ) {y : Fin (n + 1) → ℝ} (hy : y ∈ box w) :
    y ⬝ᵥ S *ᵥ y ≤ (n + 1 : ℝ) * ∑ i, (w i) ^ 2 * S i i := by
  refine (quadratic_le_card_mul_diagonal_sum hS y).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro i hi
  have hbounds : -w i ≤ y i ∧ y i ≤ w i := hy i (Set.mem_univ i)
  have hsq : (y i) ^ 2 ≤ (w i) ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hbounds.2)
      (show 0 ≤ w i + y i by linarith [hbounds.1])
    nlinarith
  exact mul_le_mul_of_nonneg_right hsq hS.diag_nonneg

theorem gaussian_box_lower_diagonal_budget
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosDef) (w : Fin (n + 1) → ℝ) :
    normalization n *
        ENNReal.ofReal (Real.exp (-((n + 1 : ℝ) * ∑ i, (w i) ^ 2 * S⁻¹ i i) / 2)) *
        ENNReal.ofReal (1 / Real.sqrt S.det) * (∏ i, ENNReal.ofReal (2 * w i)) ≤
      (multivariateGaussian 0 S) (ofLp ⁻¹' box w) :=
  gaussian_box_lower hS w _ (fun y hy ↦ quadratic_le_box_diagonal_budget hS.posSemidef.inv w hy)

end Erdos524.GaussianCovarianceBox
