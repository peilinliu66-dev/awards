import Erdos524.GaussianVectorLaw
import Erdos524.FiniteGaussianTailBound

/-! Exact coordinate projections and sup-norm contraction for finite Gaussian laws. -/

namespace Erdos524.GaussianCoordinateProjection

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ProbabilityTheory
open Erdos524.GaussianVectorLaw Erdos524.FiniteGaussianTailBound

variable {n m : ℕ}

theorem gaussian_coordinate_projection {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (f : Fin m → Fin n) :
    (multivariateGaussian 0 S).map (fun z ↦ fun i ↦ z (f i)) =
      (multivariateGaussian 0 (S.submatrix f f)).map ofLp := by
  have hX : HasGaussianLaw (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ z (f i))
      (multivariateGaussian 0 S) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (f i)))
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (multivariateGaussian 0 (S.submatrix f f)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (S.submatrix f f)) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  apply map_eq_of_mean_covariance hX hY (by fun_prop) (by fun_prop)
  · intro i
    rw [gaussian_coordinate_mean, gaussian_coordinate_mean]
  · intro i j
    rw [covariance_eval_multivariateGaussian hS,
      covariance_eval_multivariateGaussian (hS.submatrix f)]
    rfl

theorem integral_projection_sup_norm_le {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (f : Fin m → Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin m), ‖ofLp z‖ ∂multivariateGaussian 0 (S.submatrix f f)) ≤
      ∫ z : EuclideanSpace ℝ (Fin n), ‖ofLp z‖ ∂multivariateGaussian 0 S := by
  have he := congrArg (fun μ : Measure (Fin m → ℝ) ↦ ∫ z, ‖z‖ ∂μ)
    (gaussian_coordinate_projection hS f)
  rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop)] at he
  rw [← he]
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin m → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (f i))
  let B := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap
  apply integral_mono (A.integrable_comp IsGaussian.integrable_id).norm
    (B.integrable_comp IsGaussian.integrable_id).norm
  intro z
  exact (pi_norm_le_iff_of_nonneg (norm_nonneg (ofLp z))).mpr (fun i ↦ norm_le_pi_norm (ofLp z) (f i))

end Erdos524.GaussianCoordinateProjection
