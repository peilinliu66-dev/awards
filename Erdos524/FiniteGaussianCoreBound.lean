import Erdos524.FiniteGaussianTailBound
import Erdos524.CauchyLogGeometry

/-! Uniform finite-evaluation control for the stationary normalized Cauchy kernel. -/

namespace Erdos524.FiniteGaussianCoreBound

open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators
open Erdos524.FiniteChaining Erdos524.FiniteGaussianTailBound Erdos524.CauchyKernel

variable {n : ℕ}

theorem integral_stationary_sup_norm_le (t : Fin (n + 1) → ℝ)
    (hmono : ∀ j : Fin n, t j.castSucc ≤ t j.succ) :
    (∫ z : EuclideanSpace ℝ (Fin (n + 1)), ‖ofLp z‖
      ∂multivariateGaussian 0 (normalized (fun i ↦ Real.exp (t i)))) ≤
        1 + (t (Fin.last n) - t 0) / Real.sqrt 8 := by
  let S := normalized (fun i ↦ Real.exp (t i))
  have hS : S.PosSemidef := posSemidef_normalized_fin _ (fun i ↦ Real.exp_pos _)
  have hlast : (∫ z : EuclideanSpace ℝ (Fin (n + 1)), (z (Fin.last n)) ^ 2
      ∂multivariateGaussian 0 S) ≤ (1 : ℝ) ^ 2 := by
    rw [gaussian_coordinate_second_moment hS]
    change normalizedKernel (Real.exp (t (Fin.last n))) (Real.exp (t (Fin.last n))) ≤ (1 : ℝ) ^ 2
    rw [normalizedKernel_exp]
    norm_num
  have hdiff (j : Fin n) :
      (∫ z : EuclideanSpace ℝ (Fin (n + 1)), (z j.castSucc - z j.succ) ^ 2
        ∂multivariateGaussian 0 S) ≤ ((t j.succ - t j.castSucc) / Real.sqrt 8) ^ 2 := by
    rw [gaussian_increment_second_moment hS]
    change normalizedKernel (Real.exp (t j.castSucc)) (Real.exp (t j.castSucc)) -
      2 * normalizedKernel (Real.exp (t j.castSucc)) (Real.exp (t j.succ)) +
      normalizedKernel (Real.exp (t j.succ)) (Real.exp (t j.succ)) ≤ _
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    have h := normalized_exp_increment_le (t j.castSucc) (t j.succ)
    nlinarith [sq_nonneg (t j.succ - t j.castSucc)]
  have h := integral_norm_le_budget
    (X := fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ ofLp z)
    (fun i ↦ gaussian_coordinate_memLp_two S i) 1
    (fun j : Fin n ↦ (t j.succ - t j.castSucc) / Real.sqrt 8) (by norm_num)
    (fun j ↦ div_nonneg (sub_nonneg.mpr (hmono j)) (Real.sqrt_nonneg _)) hlast hdiff
  have he : (∑ j : Fin n, (t j.succ - t j.castSucc) / Real.sqrt 8) =
      (t (Fin.last n) - t 0) / Real.sqrt 8 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    congr 1
    linarith [Fin.sum_univ_castSucc t, Fin.sum_univ_succ t]
  rw [he] at h
  exact h

end Erdos524.FiniteGaussianCoreBound
