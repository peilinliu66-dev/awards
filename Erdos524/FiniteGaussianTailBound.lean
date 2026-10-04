import Erdos524.FiniteChaining
import Erdos524.CauchyIncrementBounds
import Erdos524.CauchyPositivity
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! Uniform finite-evaluation tail control for the Cauchy Laplace covariance. -/

namespace Erdos524.FiniteGaussianTailBound

open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.FiniteChaining Erdos524.CauchyIncrementBounds Erdos524.CauchyKernel

variable {n : ℕ}

theorem gaussian_coordinate_memLp_two (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    MemLp (fun z : EuclideanSpace ℝ (Fin n) ↦ z i) 2 (multivariateGaussian 0 S) := by
  have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
    IsGaussian.hasGaussianLaw_id
  simpa only [EuclideanSpace.coe_proj, id_eq] using
    (h.map_fun (EuclideanSpace.proj i)).memLp_two

theorem gaussian_coordinate_mean (S : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n), z i ∂multivariateGaussian 0 S) = 0 := by
  have h := ContinuousLinearMap.integral_comp_id_comm
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S)
    IsGaussian.integrable_id (EuclideanSpace.proj (𝕜 := ℝ) i)
  simpa only [EuclideanSpace.coe_proj, integral_id_multivariateGaussian, map_zero] using h

theorem gaussian_coordinate_second_moment {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (i : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n), (z i) ^ 2 ∂multivariateGaussian 0 S) = S i i := by
  rw [← variance_of_integral_eq_zero (gaussian_coordinate_memLp_two S i).aemeasurable
    (gaussian_coordinate_mean S i)]
  exact variance_eval_multivariateGaussian hS i

theorem gaussian_increment_second_moment {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S.PosSemidef) (i j : Fin n) :
    (∫ z : EuclideanSpace ℝ (Fin n), (z i - z j) ^ 2 ∂multivariateGaussian 0 S) =
      S i i - 2 * S i j + S j j := by
  have hi := gaussian_coordinate_memLp_two S i
  have hj := gaussian_coordinate_memLp_two S j
  have hd : MemLp (fun z : EuclideanSpace ℝ (Fin n) ↦ z i - z j) 2 (multivariateGaussian 0 S) :=
    hi.sub hj
  have hmean : (∫ z : EuclideanSpace ℝ (Fin n), z i - z j ∂multivariateGaussian 0 S) = 0 := by
    rw [integral_sub (hi.integrable (by norm_num)) (hj.integrable (by norm_num)),
      gaussian_coordinate_mean S i, gaussian_coordinate_mean S j, sub_self]
  rw [← variance_of_integral_eq_zero hd.aemeasurable hmean,
    variance_fun_sub hi hj, variance_eval_multivariateGaussian hS i,
    variance_eval_multivariateGaussian hS j, covariance_eval_multivariateGaussian hS i j]

/-- The bound is independent of the number and spacing of the requested
positive evaluation parameters. Repeated parameters are allowed. -/
theorem integral_cauchy_sup_norm_le (u : Fin (n + 1) → ℝ)
    (hu : ∀ i, 0 < u i) (hmono : ∀ j : Fin n, u j.castSucc ≤ u j.succ) :
    (∫ z : EuclideanSpace ℝ (Fin (n + 1)), ‖ofLp z‖ ∂multivariateGaussian 0 (cauchy u)) ≤
      1 / Real.sqrt (u 0) := by
  have hC := posSemidef_cauchy_fin u hu
  apply integral_norm_le_decreasing_budget
    (X := fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ ofLp z)
    (fun i ↦ gaussian_coordinate_memLp_two (cauchy u) i)
    (fun i ↦ 1 / Real.sqrt (u i))
  · intro i
    positivity
  · intro j
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr (hu _))
      (Real.sqrt_le_sqrt (hmono j))
  · rw [gaussian_coordinate_second_moment hC]
    change 1 / (u (Fin.last n) + u (Fin.last n)) ≤ (1 / Real.sqrt (u (Fin.last n))) ^ 2
    rw [div_pow, one_pow, Real.sq_sqrt (hu _).le]
    exact one_div_le_one_div_of_le (hu _) (by linarith [hu (Fin.last n)])
  · intro j
    rw [gaussian_increment_second_moment hC]
    change 1 / (u j.castSucc + u j.castSucc) - 2 * (1 / (u j.castSucc + u j.succ)) +
      1 / (u j.succ + u j.succ) ≤ _
    convert cauchy_increment_le_inverse_root_sq (hu j.castSucc) (hu j.succ) using 1 <;> ring

end Erdos524.FiniteGaussianTailBound
