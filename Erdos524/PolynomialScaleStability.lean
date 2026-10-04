import Erdos524.InversePolynomialScale

/-! Uniform comparison of the inverse normalization between N/2 and N. -/

namespace Erdos524.InversePolynomialScale

open Set Filter
open Erdos524.InverseSmallBallMargins

theorem logProbability_half_gap {x y : ℝ} (hyp : 0 < y) (hy : 2 ≤ Real.log y)
    (hxy : y / 2 ≤ x) (hxy' : x ≤ y) :
    |logProbability x - logProbability y| ≤ 1 := by
  have hxp : 0 < x := lt_of_lt_of_le (by positivity) hxy
  have hl2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlow := Real.log_le_log (show 0 < y / 2 by positivity) hxy
  rw [Real.log_div hyp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlow
  have hxlog : 0 < Real.log x := by linarith
  have hloghalf : Real.log y / 2 ≤ Real.log x := by linarith
  have hupper := Real.log_le_log hxp hxy'
  have hlogupper := Real.log_le_log hxlog hupper
  have hloglower := Real.log_le_log (show 0 < Real.log y / 2 by linarith) hloghalf
  rw [Real.log_div (by linarith : Real.log y ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hloglower
  unfold logProbability
  rw [abs_le]
  constructor <;> linarith

theorem eventually_half_interval_normalizer {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᶠ y : ℝ in atTop, ∀ x : ℝ, y / 2 ≤ x → x ≤ y → normalizer x ≤ (1 + ε) * normalizer y := by
  filter_upwards [logProbability_tendsto_atTop.eventually (eventually_inverseRadius_bounded_shift heps heps2),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ), eventually_gt_atTop (0 : ℝ)] with y h hy hyp
  intro x hxy hxy'
  have hd := (h (logProbability x) (logProbability_half_gap hyp hy hxy hxy')).2
  have hs : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy'
  have hdp : 0 ≤ delta x := delta_nonneg _
  have hdy : 0 ≤ (1 + ε) * delta y := mul_nonneg (by linarith) (delta_nonneg _)
  unfold normalizer
  calc
    _ ≤ Real.sqrt y * ((1 + ε) * delta y) := mul_le_mul hs hd hdp (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem eventually_delta_log_lower :
    ∀ᶠ x : ℝ in atTop, 1 ≤ Real.sqrt (Real.log x) * delta x := by
  filter_upwards [logProbability_tendsto_atTop.eventually (eventually_inverseRadius_exp_lower (by norm_num : (0 : ℝ) < 1)),
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x h hx
  have hs : Real.sqrt (Real.log x) = Real.exp (logProbability x) := by
    have hh := Erdos524.CauchyKernel.sqrt_exp_half (Real.log (Real.log x))
    rw [Real.exp_log (by linarith : 0 < Real.log x)] at hh
    exact hh
  have hh := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (Real.log x))
  rw [hs] at hh
  have he : Real.exp (logProbability x) * Real.exp (-1 * logProbability x) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  rw [he] at hh
  rw [hs]
  exact hh

end Erdos524.InversePolynomialScale
