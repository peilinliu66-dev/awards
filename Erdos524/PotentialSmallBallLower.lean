import Erdos524.FiniteSmallBallLower
import Erdos524.RegressionWeightBounds

/-! The explicit potential-to-probability lower-bound contract. -/

namespace Erdos524.PotentialSmallBallLower

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators
open Erdos524.CauchyKernel Erdos524.GaussianBoxDensity
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallLower
open Erdos524.RegressionWeightBounds

variable {n : ℕ}

theorem finiteSmallBall_lower_of_potentials
    (s : Fin (n + 1) → ℝ) (hs : Function.Injective s) (L G A B q δ η : ℝ)
    (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 ≤ B) (hη : 0 < η) (hcut : 0 ≤ 2 * L + G)
    (hrow : ∀ i, omittedPotential s i (s i) ≤ L - s i / 2 + A)
    (hnode : ∀ i, s i ≤ 2 * L + 2 * G)
    (hpoint : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * L + G → (∀ j, t ≠ s j) →
      ∀ i, L - t / 2 + B ≤ omittedPotential s i t)
    (hmean : 2 * (n + 1 : ℝ) * q * Real.exp A ≤ δ - η)
    (hbudget : Real.exp (-L - B) * (1 + (2 * L + G) / Real.sqrt 8) +
      Real.exp (-(2 * L + G) / 2) ≤ η / 2) :
    (1 / 2 : ℝ≥0∞) *
        (multivariateGaussian 0 (cauchy (fun i ↦ Real.exp (s i))))
          (ofLp ⁻¹' box (fun _ ↦ q)) ≤ finiteSmallBall (Real.exp 1 * δ) := by
  apply finiteSmallBall_lower_of_interpolation (fun i ↦ Real.exp (s i))
    (fun i ↦ Real.exp_pos _) (Real.exp_injective.comp hs) (fun _ ↦ q) hη
    (Real.one_le_exp_iff.mpr hcut) (Real.exp_pos (-L - B)).le
  · intro v hv
    exact (sum_abs_weights_global_le s hs L G A B q hq hA hB hrow hnode hpoint hv).trans hmean
  · intro u hu huT
    have hupos : 0 < u := lt_of_lt_of_le (by norm_num) hu
    have ht : Real.log u ≤ 2 * L + G := by
      have h := Real.log_le_log hupos huT
      simpa only [Real.log_exp] using h
    have h := blaschke_core_bound s (Real.log u) L B
      (fun hnodes ↦ hpoint _ (Real.log_nonneg hu) ht hnodes 0)
    simpa only [Real.exp_log hupos] using h
  · rw [Real.log_exp, sqrt_exp_half, one_div, ← Real.exp_neg]
    convert hbudget using 1 <;> congr 2 <;> ring

end Erdos524.PotentialSmallBallLower
