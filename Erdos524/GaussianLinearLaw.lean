import Erdos524.GaussianVectorLaw
import Erdos524.FiniteGaussianTailBound

/-! Actual finite Gaussian linear image law, including non-square and singular maps. -/

namespace Erdos524.GaussianLinearLaw

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ProbabilityTheory
open Erdos524.GaussianVectorLaw Erdos524.FiniteGaussianTailBound

variable {n m : ℕ}

theorem gaussian_linear_map {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (multivariateGaussian 0 S).map (fun z ↦ A *ᵥ ofLp z) =
      (multivariateGaussian 0 (A * S * Aᵀ)).map ofLp := by
  have hT : (A * S * Aᵀ).PosSemidef := by
    have he : Aᴴ = Aᵀ := by ext i j; simp
    have h := hS.mul_mul_conjTranspose_same A
    rwa [he] at h
  have hX : HasGaussianLaw (fun z : EuclideanSpace ℝ (Fin n) ↦ A *ᵥ ofLp z)
      (multivariateGaussian 0 S) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
      IsGaussian.hasGaussianLaw_id
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap
    let L := (Matrix.toLin' A).toContinuousLinearMap.comp e
    exact h.map_fun L
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (multivariateGaussian 0 (A * S * Aᵀ)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (A * S * Aᵀ)) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  apply map_eq_of_mean_covariance hX hY (by fun_prop) (by fun_prop)
  · intro i
    change (∫ z, ∑ k, A i k * z k ∂multivariateGaussian 0 S) = _
    rw [integral_finsetSum Finset.univ (fun k _ ↦
      ((gaussian_coordinate_memLp_two S k).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, gaussian_coordinate_mean, mul_zero, Finset.sum_const_zero]
  · intro i j
    change cov[fun z ↦ ∑ k, A i k * z k, fun z ↦ ∑ l, A j l * z l; multivariateGaussian 0 S] = _
    rw [covariance_fun_sum_fun_sum (fun k ↦ (gaussian_coordinate_memLp_two S k).const_mul _)
      (fun l ↦ (gaussian_coordinate_memLp_two S l).const_mul _)]
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, covariance_eval_multivariateGaussian hS]
    rw [covariance_eval_multivariateGaussian hT, Matrix.mul_assoc]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring

end Erdos524.GaussianLinearLaw
