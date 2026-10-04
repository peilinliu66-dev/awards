import Erdos524.GaussianVectorLaw
import Erdos524.FiniteGaussianTailBound
import Erdos524.FiniteKernelPerturbation
import Erdos524.GaussianBoxDensity

/-! Exact diagonal scaling for actual Gaussian vectors, including singular covariances. -/

namespace Erdos524.GaussianDiagonalScaling

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ProbabilityTheory
open Erdos524.GaussianVectorLaw Erdos524.FiniteGaussianTailBound
open Erdos524.GaussianBoxDensity Erdos524.FiniteKernelPerturbation
open Erdos524.LaplaceKernelComparison

variable {n : ℕ}

theorem diagonal_gaussian_map {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (d : Fin n → ℝ) :
    (multivariateGaussian 0 S).map (fun z ↦ fun i ↦ d i * z i) =
      (multivariateGaussian 0 (diagonal d * S * diagonal d)).map ofLp := by
  have hD : (diagonal d * S * diagonal d).PosSemidef := by
    simpa only [Matrix.diagonal_conjTranspose, star_trivial] using
      hS.conjTranspose_mul_mul_same (diagonal d)
  have hX : HasGaussianLaw (fun z : EuclideanSpace ℝ (Fin n) ↦ fun i ↦ d i * z i)
      (multivariateGaussian 0 S) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S) :=
      IsGaussian.hasGaussianLaw_id
    let A : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ) :=
      ContinuousLinearMap.pi (fun i ↦ d i • EuclideanSpace.proj i)
    exact h.map_fun A
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
      (multivariateGaussian 0 (diagonal d * S * diagonal d)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
        (diagonal d * S * diagonal d)) := IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)).toContinuousLinearMap
  apply map_eq_of_mean_covariance hX hY (by fun_prop) (by fun_prop)
  · intro i
    rw [integral_const_mul, gaussian_coordinate_mean, gaussian_coordinate_mean, mul_zero]
  · intro i j
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_eval_multivariateGaussian hS, covariance_eval_multivariateGaussian hD]
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring

theorem diagonal_gaussian_box {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosSemidef) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 0 < d i) (w : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 (diagonal d * S * diagonal d))
        (ofLp ⁻¹' box (fun i ↦ d i * w i)) =
      (multivariateGaussian 0 S) (ofLp ⁻¹' box w) := by
  have h := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ (box (fun i ↦ d i * w i)))
    (diagonal_gaussian_map hS d)
  rw [Measure.map_apply (by fun_prop) (measurableSet_box _),
    Measure.map_apply (by fun_prop) (measurableSet_box _)] at h
  have he : (fun z : EuclideanSpace ℝ (Fin (n + 1)) ↦ fun i ↦ d i * z i) ⁻¹'
      box (fun i ↦ d i * w i) = ofLp ⁻¹' box w := by
    ext z
    simp only [Set.mem_preimage, box, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
    apply forall_congr'
    intro i
    rw [← mul_neg, mul_le_mul_iff_right₀ (hd i), mul_le_mul_iff_right₀ (hd i)]
  rw [he] at h
  exact h.symm

theorem normalized_finiteKernel_box (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 < u i)
    (δ : ℝ) :
    (multivariateGaussian 0 (normalizedFiniteKernel u))
        (ofLp ⁻¹' box (fun i ↦ Real.sqrt (u i) * δ)) =
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
  exact diagonal_gaussian_box (finiteKernel_posSemidef u (fun i ↦ (hu i).le))
    (fun i ↦ Real.sqrt (u i)) (fun i ↦ Real.sqrt_pos.mpr (hu i)) (fun _ ↦ δ)

theorem normalized_finiteKernel_exp_box (t : Fin (n + 1) → ℝ) (L : ℝ) :
    (multivariateGaussian 0 (normalizedFiniteKernel (fun i ↦ Real.exp (t i))))
        (ofLp ⁻¹' box (fun i ↦ Real.exp (-(L - t i / 2)))) =
      (multivariateGaussian 0 (finiteKernel (fun i ↦ Real.exp (t i))))
        (ofLp ⁻¹' box (fun _ ↦ Real.exp (-L))) := by
  have h := normalized_finiteKernel_box (fun i ↦ Real.exp (t i))
    (fun i ↦ Real.exp_pos _) (Real.exp (-L))
  have he (i : Fin (n + 1)) : Real.sqrt (Real.exp (t i)) * Real.exp (-L) =
      Real.exp (-(L - t i / 2)) := by
    rw [Erdos524.CauchyKernel.sqrt_exp_half, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he] at h
  exact h

end Erdos524.GaussianDiagonalScaling
