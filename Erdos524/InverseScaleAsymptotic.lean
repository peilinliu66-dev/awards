import Erdos524.InversePolynomialScale

/-! Sharp inversion of the cubic Gaussian small-ball logarithm. -/

namespace Erdos524.InversePolynomialScale

open Filter
open Erdos524.InverseSmallBallMargins Erdos524.FiniteSmallBallBasic

noncomputable def logarithmicScale (x : ℝ) : ℝ := (Real.log (Real.log x)) ^ (1 / 3 : ℝ)
noncomputable def logarithmicConstant : ℝ := (3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ)

theorem inverseLog_cubic_tendsto :
    Tendsto (fun t : ℝ ↦ (inverseLog t) ^ 3 / t) atTop (nhds (3 * Real.pi ^ 2 / 2)) := by
  have h := sharp_log_asymptotic.comp inverseLog_tendsto_atTop
  have he : (fun t : ℝ ↦ Real.log (smallBallReal (Real.exp (-inverseLog t))) / (inverseLog t) ^ 3) =ᶠ[atTop]
      (fun t ↦ -t / (inverseLog t) ^ 3) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [exp_neg_inverseLog ht, (inverseRadius_spec ht).2, Real.log_exp]
  have h' := h.congr' he
  have hneg := h'.neg
  simp only [neg_div, neg_neg] at hneg
  have hi := hneg.inv₀ (by positivity : 2 / (3 * Real.pi ^ 2) ≠ 0)
  simpa only [inv_div] using hi

theorem polynomial_inverse_cubic_tendsto :
    Tendsto (fun x : ℝ ↦ (inverseLog (logProbability x)) ^ 3 / Real.log (Real.log x))
      atTop (nhds (3 * Real.pi ^ 2 / 4)) := by
  have h := (inverseLog_cubic_tendsto.comp logProbability_tendsto_atTop).div_const 2
  have hc : (3 * Real.pi ^ 2 / 2) / 2 = 3 * Real.pi ^ 2 / 4 := by ring
  rw [hc] at h
  convert h using 1
  funext x
  dsimp only [Function.comp_def, logProbability]
  ring

theorem inverse_logarithm_asymptotic :
    Tendsto (fun x : ℝ ↦ (-Real.log (delta x)) / logarithmicScale x)
      atTop (nhds logarithmicConstant) := by
  have h := polynomial_inverse_cubic_tendsto.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))
  apply h.congr'
  filter_upwards [logProbability_tendsto_atTop.eventually (inverseLog_tendsto_atTop.eventually_gt_atTop (0 : ℝ)),
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x hL hx
  have hlog : 0 ≤ Real.log (Real.log x) := (Real.log_pos hx).le
  rw [Real.div_rpow (pow_nonneg hL.le 3) hlog, ← Real.rpow_natCast_mul hL.le]
  norm_num
  rfl

theorem logarithmicScale_tendsto_atTop : Tendsto logarithmicScale atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)

theorem logarithmicConstant_pos : 0 < logarithmicConstant := by
  unfold logarithmicConstant
  positivity

theorem log_multiple_delta_asymptotic {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ ↦ Real.log (c * delta x) / logarithmicScale x)
      atTop (nhds (-logarithmicConstant)) := by
  have hneg := inverse_logarithm_asymptotic.neg
  have hdelta : Tendsto (fun x : ℝ ↦ Real.log (delta x) / logarithmicScale x)
      atTop (nhds (-logarithmicConstant)) := by
    simpa only [neg_div, neg_neg] using hneg
  have hconst := logarithmicScale_tendsto_atTop.const_div_atTop (Real.log c)
  have h := hconst.add hdelta
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x hx
  rw [Real.log_mul hc.ne' (delta_pos hx).ne', add_div]

end Erdos524.InversePolynomialScale
