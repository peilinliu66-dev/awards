import Erdos524.InversePolynomialScale

/-! Squared Gaussian probability margins at the exact polynomial normalization. -/

namespace Erdos524.InversePolynomialScale

open Filter
open Erdos524.FiniteSmallBallBasic Erdos524.InverseSmallBallMargins

theorem eventually_squared_probability_margins {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      Real.exp (c * Real.sqrt (Real.log (Real.log x))) / Real.log x ≤
        (smallBallReal ((1 + ε) * delta x)) ^ 2 ∧
      (smallBallReal ((1 - ε) * delta x)) ^ 2 ≤
        Real.exp (-c * Real.sqrt (Real.log (Real.log x))) / Real.log x := by
  obtain ⟨c, hc, hm⟩ := eventually_inverse_sqrt_margins heps heps2
  refine ⟨c, hc, ?_⟩
  filter_upwards [logProbability_tendsto_atTop.eventually hm,
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x h hx
  have ht : 0 < logProbability x := logProbability_pos hx
  have hloglog : 0 ≤ Real.log (Real.log x) := (Real.log_pos hx).le
  have hroot : Real.sqrt (Real.log (Real.log x)) ≤ 2 * Real.sqrt (logProbability x) := by
    have h1 := Real.sq_sqrt hloglog
    have h2 := Real.sq_sqrt ht.le
    have hr := Real.sqrt_nonneg (logProbability x)
    dsimp only [logProbability] at h2 hr ⊢
    nlinarith [Real.sqrt_nonneg (Real.log (Real.log x))]
  have hrootc := mul_le_mul_of_nonneg_left hroot hc.le
  have hp0 : 0 ≤ smallBallReal ((1 + ε) * delta x) := ENNReal.toReal_nonneg
  have hm0 : 0 ≤ smallBallReal ((1 - ε) * delta x) := ENNReal.toReal_nonneg
  have hplus := (sq_le_sq₀ (Real.exp_pos _).le hp0).mpr h.1
  have hminus := (sq_le_sq₀ hm0 (Real.exp_pos _).le).mpr h.2
  rw [← Real.exp_nat_mul] at hplus hminus
  have hep : Real.exp ((2 : ℕ) * (-logProbability x + c * Real.sqrt (logProbability x))) =
      Real.exp (2 * c * Real.sqrt (logProbability x)) / Real.log x := by
    rw [show ((2 : ℕ) : ℝ) * (-logProbability x + c * Real.sqrt (logProbability x)) =
      2 * c * Real.sqrt (logProbability x) - Real.log (Real.log x) by unfold logProbability; ring,
      Real.exp_sub, Real.exp_log (by linarith : 0 < Real.log x)]
  have hem : Real.exp ((2 : ℕ) * (-logProbability x - c * Real.sqrt (logProbability x))) =
      Real.exp (-2 * c * Real.sqrt (logProbability x)) / Real.log x := by
    rw [show ((2 : ℕ) : ℝ) * (-logProbability x - c * Real.sqrt (logProbability x)) =
      -2 * c * Real.sqrt (logProbability x) - Real.log (Real.log x) by unfold logProbability; ring,
      Real.exp_sub, Real.exp_log (by linarith : 0 < Real.log x)]
  rw [hep] at hplus
  rw [hem] at hminus
  constructor
  · exact (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [hrootc])) (by linarith)).trans hplus
  · exact hminus.trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith only [hrootc])) (by linarith))

end Erdos524.InversePolynomialScale
