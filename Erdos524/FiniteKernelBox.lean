import Erdos524.FiniteKernelPerturbation
import Erdos524.GaussianLogBox
import Erdos524.LogCauchyDeterminant

/-! Actual finite-Laplace Gaussian box upper bound, with the cutoff error discharged. -/

namespace Erdos524.FiniteKernelBox

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
open Erdos524.GaussianBoxDensity Erdos524.GaussianLogBox
open Erdos524.GaussianCovarianceComparison Erdos524.CauchyKernel
open Erdos524.FiniteKernelPerturbation

variable {n : ℕ}

theorem isClosed_box (w : Fin (n + 1) → ℝ) : IsClosed (box w) :=
  isClosed_set_pi (fun _ _ ↦ isClosed_Icc)

theorem convex_box (w : Fin (n + 1) → ℝ) : Convex ℝ (box w) :=
  convex_pi (fun _ _ ↦ convex_Icc _ _)

theorem neg_mem_box (w : Fin (n + 1) → ℝ) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ box w) : -x ∈ box w := by
  intro i hi
  have hb := hx i hi
  constructor <;> change _ ≤ _ <;> simp only [Pi.neg_apply] <;> linarith [hb.1, hb.2]

theorem gaussian_box_covariance_mono
    {S T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosSemidef) (hTS : (T - S).PosSemidef) (w : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 T) (ofLp ⁻¹' box w) ≤
      (multivariateGaussian 0 S) (ofLp ⁻¹' box w) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)
  apply multivariate_gaussian_covariance_mono hS hTS
  · exact (isClosed_box w).preimage e.continuous
  · exact (convex_box w).linear_preimage e.toLinearMap
  · intro x hx
    exact neg_mem_box w hx

theorem finiteKernel_box_exp_upper
    (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 < u i) (hinj : Function.Injective u)
    (v : ℝ) (hmin : ∀ i, v ≤ u i)
    (hbudget : (n + 1 : ℝ) * Real.exp (-2 * v) * (normalized u)⁻¹.trace ≤ 1)
    (y : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 (normalizedFiniteKernel u))
        (ofLp ⁻¹' box (fun i ↦ Real.exp (-y i))) ≤
      ENNReal.ofReal (Real.exp (boxExponent ((1 / 2 : ℝ) • normalized u) y)) := by
  have hC := (posDef_normalized_fin u hu hinj).smul (show (0 : ℝ) < 1 / 2 by norm_num)
  exact (gaussian_box_covariance_mono hC.posSemidef
    (normalizedFiniteKernel_half_gap u hu hinj v hmin hbudget) _).trans
      (gaussian_box_exp_upper hC y)

theorem separated_finiteKernel_box_exp_upper (t : Fin (n + 1) → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n + 1), i < j → ((j : ℝ) - (i : ℝ)) / r ≤ t j - t i)
    (v : ℝ) (hmin : ∀ i, v ≤ Real.exp (t i))
    (hsmall : 2 * (n + 1 : ℝ) ^ 2 * Real.exp (r * Real.pi ^ 2 - 2 * v) ≤ 1)
    (y : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 (normalizedFiniteKernel (fun i ↦ Real.exp (t i))))
        (ofLp ⁻¹' box (fun i ↦ Real.exp (-y i))) ≤
      ENNReal.ofReal (Real.exp
        (boxExponent ((1 / 2 : ℝ) • normalized (fun i ↦ Real.exp (t i))) y)) := by
  have hC := (posDef_normalized_fin (fun i ↦ Real.exp (t i)) (fun i ↦ Real.exp_pos _)
    (Real.exp_injective.comp (separated_grid_strictMono t hr hsep).injective)).smul
      (show (0 : ℝ) < 1 / 2 by norm_num)
  exact (gaussian_box_covariance_mono hC.posSemidef
    (separated_normalizedFiniteKernel_half_gap t hr hsep v hmin hsmall) _).trans
      (gaussian_box_exp_upper hC y)

theorem half_normalized_boxExponent (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (y : Fin (n + 1) → ℝ) :
    boxExponent ((1 / 2 : ℝ) • normalized (fun i ↦ Real.exp (t i))) y =
      -(∑ i, y i) + pairEnergy t +
        (n + 1 : ℝ) * (2 * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))) := by
  have hdet := (posDef_normalized_fin (fun i ↦ Real.exp (t i))
    (fun i ↦ Real.exp_pos _) (Real.exp_injective.comp ht.injective)).det_pos
  unfold boxExponent
  rw [Matrix.det_smul, Real.log_mul (pow_ne_zero _ (by norm_num)) (ne_of_gt hdet),
    Real.log_pow, log_det_normalized_exp t ht]
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one,
    one_div, Real.log_inv]
  ring

theorem separated_finiteKernel_box_energy_upper (t : Fin (n + 1) → ℝ)
    {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j : Fin (n + 1), i < j → ((j : ℝ) - (i : ℝ)) / r ≤ t j - t i)
    (v : ℝ) (hmin : ∀ i, v ≤ Real.exp (t i))
    (hsmall : 2 * (n + 1 : ℝ) ^ 2 * Real.exp (r * Real.pi ^ 2 - 2 * v) ≤ 1)
    (y : Fin (n + 1) → ℝ) :
    (multivariateGaussian 0 (normalizedFiniteKernel (fun i ↦ Real.exp (t i))))
        (ofLp ⁻¹' box (fun i ↦ Real.exp (-y i))) ≤
      ENNReal.ofReal (Real.exp (-(∑ i, y i) + pairEnergy t +
        (n + 1 : ℝ) * (2 * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))))) := by
  have h := separated_finiteKernel_box_exp_upper t hr hsep v hmin hsmall y
  rw [half_normalized_boxExponent t (separated_grid_strictMono t hr hsep) y] at h
  exact h

end Erdos524.FiniteKernelBox
