import Erdos524.FiniteSmallBallEnvelope
import Erdos524.CauchySmallBoxLower
import Erdos524.ResidualUniformBudget

/-! Uniform finite-only lower bound for the actual Laplace small-ball envelope. -/

namespace Erdos524.FiniteSmallBallLower

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.CauchyKernel Erdos524.CauchyGaussianRegression
open Erdos524.GaussianBoxDensity Erdos524.GaussianDiagonalScaling
open Erdos524.LaplaceKernelComparison Erdos524.FiniteKernelBox
open Erdos524.CauchySmallBoxLower Erdos524.ResidualUniformBudget
open Erdos524.FiniteSmallBallEnvelope

variable {n m : ℕ}

theorem shifted_cauchy_box_le_finite (u : Fin (m + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (δ : ℝ) :
    (multivariateGaussian 0 (cauchy (fun i ↦ u i + 1))) (ofLp ⁻¹' box (fun _ ↦ δ)) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ Real.exp 1 * δ)) := by
  let C := cauchy (fun i ↦ u i + 1)
  have hC : C.PosSemidef := posSemidef_cauchy_fin _ (fun i ↦ by linarith [hu i])
  have hs := diagonal_gaussian_box hC (fun _ ↦ Real.exp 1) (fun _ ↦ Real.exp_pos 1) (fun _ ↦ δ)
  have he : diagonal (fun _ : Fin (m + 1) ↦ Real.exp 1) * C *
      diagonal (fun _ : Fin (m + 1) ↦ Real.exp 1) = Real.exp 2 • C := by
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
    have hE : Real.exp 1 * Real.exp 1 = Real.exp 2 := by rw [← Real.exp_add]; norm_num
    calc
      Real.exp 1 * C i j * Real.exp 1 = (Real.exp 1 * Real.exp 1) * C i j := by ring
      _ = _ := by rw [hE]
  rw [he] at hs
  rw [← hs]
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (m + 1) ↦ ℝ)
  apply finite_laplace_gaussian_comparison u hu
  · exact (isClosed_box _).preimage e.continuous
  · exact (convex_box _).linear_preimage e.toLinearMap
  · intro z hz
    exact neg_mem_box _ hz

theorem finiteSmallBall_lower_of_interpolation
    (x : Fin (n + 1) → ℝ) (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (w : Fin (n + 1) → ℝ) {δ η T b : ℝ} (hη : 0 < η) (hT : 1 ≤ T) (hb : 0 ≤ b)
    (hweights : ∀ v : ℝ, 1 ≤ v → (∑ i, |regressionWeight x i v| * w i) ≤ δ - η)
    (hB : ∀ u : ℝ, 1 ≤ u → u ≤ T → |blaschke x u| ≤ b * Real.sqrt u)
    (hbudget : b * (1 + Real.log T / Real.sqrt 8) + 1 / Real.sqrt T ≤ η / 2) :
    (1 / 2 : ℝ≥0∞) * (multivariateGaussian 0 (cauchy x)) (ofLp ⁻¹' box w) ≤
      finiteSmallBall (Real.exp 1 * δ) := by
  apply le_iInf
  intro m
  apply le_iInf
  intro u
  let v : Fin (m + 1) → ℝ := fun j ↦ (u j : ℝ) + 1
  have hv (j : Fin (m + 1)) : 1 ≤ v j := by dsimp [v]; exact le_add_of_nonneg_left (u j).property
  have hp := small_box_lower_of_residual_budget x v hx hinj
    (fun j ↦ lt_of_lt_of_le (by norm_num) (hv j)) w hη
    (fun j ↦ hweights _ (hv j))
    ((integral_residual_uniform_le x v hx hinj hv hT hb hB).trans hbudget)
  exact hp.trans (shifted_cauchy_box_le_finite (fun i ↦ (u i : ℝ)) (fun i ↦ (u i).property) δ)

end Erdos524.FiniteSmallBallLower
