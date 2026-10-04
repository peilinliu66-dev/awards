import Erdos524.SmallBallLogDilation
import Erdos524.FiniteSmallBallInverse

/-! Quantitative margins at the exact inverse-small-ball normalization. -/

namespace Erdos524.InverseSmallBallMargins

open Set Filter
open Erdos524.FiniteSmallBallBasic Erdos524.FiniteSmallBallInverse
open Erdos524.SmallBallLogDilation

noncomputable def inverseRadius (t : ℝ) : ℝ := smallBallInverse (Real.exp (-t))
noncomputable def inverseLog (t : ℝ) : ℝ := -Real.log (inverseRadius t)

theorem inverseRadius_spec {t : ℝ} (ht : 0 < t) :
    0 < inverseRadius t ∧ smallBallReal (inverseRadius t) = Real.exp (-t) :=
  smallBallInverse_spec ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩

theorem exp_neg_inverseLog {t : ℝ} (ht : 0 < t) : Real.exp (-inverseLog t) = inverseRadius t := by
  unfold inverseLog
  rw [neg_neg, Real.exp_log (inverseRadius_spec ht).1]

theorem inverseRadius_tendsto_zero : Tendsto inverseRadius atTop (nhds 0) := by
  exact smallBallInverse_tendsto_zero.comp (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

theorem inverseLog_tendsto_atTop : Tendsto inverseLog atTop atTop := by
  apply tendsto_atTop.2
  intro R
  have hsmall := (tendsto_order.mp inverseRadius_tendsto_zero).2 (Real.exp (-R)) (Real.exp_pos _)
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  have h := Real.log_le_log (inverseRadius_spec ht0).1 ht.le
  rw [Real.log_exp] at h
  unfold inverseLog
  linarith

theorem eventually_inverse_cubic_bounds :
    ∀ᶠ t : ℝ in atTop, 0 < inverseLog t ∧
      Real.pi ^ 2 * t ≤ (inverseLog t) ^ 3 ∧ (inverseLog t) ^ 3 ≤ 3 * Real.pi ^ 2 * t := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hbound := inverseLog_tendsto_atTop.eventually (sharp_log_bounds (show 0 < 1 / (3 * Real.pi ^ 2) by positivity))
  filter_upwards [hbound, inverseLog_tendsto_atTop.eventually_gt_atTop (0 : ℝ),
    eventually_gt_atTop (0 : ℝ)] with t hb hL ht
  rw [exp_neg_inverseLog ht, (inverseRadius_spec ht).2, Real.log_exp] at hb
  have hlo := (le_div_iff₀ (pow_pos hL 3)).mp hb.1
  have hhi := (div_le_iff₀ (pow_pos hL 3)).mp hb.2
  have hlo' := mul_le_mul_of_nonneg_left hlo hp.le
  have hhi' := mul_le_mul_of_nonneg_left hhi hp.le
  field_simp at hlo' hhi'
  exact ⟨hL, by nlinarith only [hlo'], by nlinarith only [hhi']⟩

theorem inverseLog_square_dominates_sqrt :
    ∀ᶠ t : ℝ in atTop, Real.sqrt t ≤ (inverseLog t) ^ 2 := by
  filter_upwards [eventually_inverse_cubic_bounds,
    inverseLog_tendsto_atTop.eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (0 : ℝ)] with t hb hL ht
  have hp : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hpi := mul_le_mul_of_nonneg_right hp ht
  have htL : t ≤ (inverseLog t) ^ 3 := by simpa only [one_mul] using hpi.trans hb.2.1
  have h34 : (inverseLog t) ^ 3 ≤ ((inverseLog t) ^ 2) ^ 2 := by
    have h := mul_nonneg (pow_nonneg hb.1.le 3) (show 0 ≤ inverseLog t - 1 by linarith)
    nlinarith
  have hsq : (Real.sqrt t) ^ 2 ≤ ((inverseLog t) ^ 2) ^ 2 := by rw [Real.sq_sqrt ht]; exact htL.trans h34
  nlinarith [Real.sqrt_nonneg t, sq_nonneg (inverseLog t)]

theorem eventually_inverse_probability_margins {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      Real.exp (-t + c * (inverseLog t) ^ 2) ≤ smallBallReal ((1 + ε) * inverseRadius t) ∧
      smallBallReal ((1 - ε) * inverseRadius t) ≤ Real.exp (-t - c * (inverseLog t) ^ 2) := by
  obtain ⟨c, hc, hm⟩ := eventually_probability_dilation heps heps2
  refine ⟨c, hc, ?_⟩
  filter_upwards [inverseLog_tendsto_atTop.eventually hm, eventually_gt_atTop (0 : ℝ)] with t h ht
  rw [exp_neg_inverseLog ht, (inverseRadius_spec ht).2] at h
  constructor
  · simpa only [Real.exp_add] using h.1
  · simpa only [sub_eq_add_neg, Real.exp_add, neg_mul] using h.2

theorem eventually_inverse_sqrt_margins {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t : ℝ in atTop,
      Real.exp (-t + c * Real.sqrt t) ≤ smallBallReal ((1 + ε) * inverseRadius t) ∧
      smallBallReal ((1 - ε) * inverseRadius t) ≤ Real.exp (-t - c * Real.sqrt t) := by
  obtain ⟨c, hc, hm⟩ := eventually_inverse_probability_margins heps heps2
  refine ⟨c, hc, ?_⟩
  filter_upwards [hm, inverseLog_square_dominates_sqrt] with t h hs
  have hh := mul_le_mul_of_nonneg_left hs hc.le
  exact ⟨(Real.exp_le_exp.mpr (by linarith)).trans h.1,
    h.2.trans (Real.exp_le_exp.mpr (by linarith))⟩

end Erdos524.InverseSmallBallMargins
