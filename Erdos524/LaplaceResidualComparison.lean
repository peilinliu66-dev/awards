import Erdos524.GaussianLinearAnderson
import Erdos524.FiniteLaplaceBand

/-! Anderson comparison between an actual finite Laplace vector and its independent residual. -/

namespace Erdos524.LaplaceResidualComparison

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteLaplaceRegression Erdos524.FiniteLaplaceBand
open Erdos524.GaussianLinearAnderson Erdos524.GaussianBoxDensity
open Erdos524.FiniteKernelBox Erdos524.LaplaceKernelComparison Erdos524.FiniteSmallBallEnvelope

variable {n : ℕ}

theorem residual_measurable (u : Fin (n + 1) → ℝ) : Measurable (laplaceResidual u) := by
  have he : (fun z ↦ residualMap u z) = laplaceResidual u := funext (residualMap_apply u)
  rw [← he]
  exact (residualMap u).continuous.measurable

theorem residual_box_shift_le (u : Fin (n + 1) → ℝ) (δ : ℝ) (t : Fin (n + 1) → ℝ) :
    ((jointMeasure u).map (laplaceResidual u)) {r | r + t ∈ box (fun _ ↦ δ)} ≤
      ((jointMeasure u).map (laplaceResidual u)) (box (fun _ ↦ δ)) := by
  have hmshift : MeasurableSet {r : Fin (n + 1) → ℝ | r + t ∈ box (fun _ ↦ δ)} :=
    (isClosed_box _).measurableSet.preimage (by fun_prop)
  rw [Measure.map_apply (residual_measurable u) hmshift,
    Measure.map_apply (residual_measurable u) (measurableSet_box _)]
  have h := multivariate_linear_shift_le (finiteKernel (Fin.cons 0 u)) (residualMap u)
    (isClosed_box (fun _ ↦ δ)) (convex_box _) (fun {_} hy ↦ neg_mem_box _ hy) t
  change (jointMeasure u) {z | laplaceResidual u z + t ∈ box (fun _ ↦ δ)} ≤
    (jointMeasure u) {z | laplaceResidual u z ∈ box (fun _ ↦ δ)}
  simpa only [residualMap_apply, jointMeasure] using h

theorem laplace_box_product (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) =
      ((gaussianReal 0 1).prod ((jointMeasure u).map (laplaceResidual u))) (fiberSet u δ) := by
  haveI := (residual_gaussian u).isGaussian_map
  rw [Measure.prod_apply_symm (measurable_fiberSet u δ)]
  exact laplace_box_fiber_integral u hu δ

theorem laplace_box_le_residual (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) ≤
      ((jointMeasure u).map (laplaceResidual u)) (box (fun _ ↦ δ)) := by
  haveI := (residual_gaussian u).isGaussian_map
  rw [laplace_box_product u hu δ, Measure.prod_apply (measurable_fiberSet u δ)]
  calc
    _ ≤ ∫⁻ _ : ℝ, ((jointMeasure u).map (laplaceResidual u)) (box (fun _ ↦ δ)) ∂gaussianReal 0 1 := by
      apply lintegral_mono
      intro g
      have he : Prod.mk g ⁻¹' fiberSet u δ = {r | r + (fun i ↦ zeroCoefficient (u i) * g) ∈ box (fun _ ↦ δ)} := by
        ext r
        simp only [Set.mem_preimage, fiberSet, Set.mem_setOf_eq, box, Set.mem_pi,
          Set.mem_univ, true_implies, Set.mem_Icc, Pi.add_apply, abs_le, add_comm]
      change ((jointMeasure u).map (laplaceResidual u)) (Prod.mk g ⁻¹' fiberSet u δ) ≤
        ((jointMeasure u).map (laplaceResidual u)) (box (fun _ ↦ δ))
      rw [he]
      exact residual_box_shift_le u δ _
    _ = _ := by simp

theorem finiteSmallBall_le_residual (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    finiteSmallBall δ ≤ ((jointMeasure u).map (laplaceResidual u)) (box (fun _ ↦ δ)) :=
  (finiteSmallBall_le_evaluation δ n (fun i ↦ ⟨u i, hu i⟩)).trans (laplace_box_le_residual u hu δ)

end Erdos524.LaplaceResidualComparison
