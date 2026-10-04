import Erdos524.InverseSmallBallMargins

/-! Slow inverse-radius variation under bounded changes of the log-probability parameter. -/

namespace Erdos524.InverseSmallBallMargins

open Set Filter
open Erdos524.FiniteSmallBallBasic Erdos524.FiniteSmallBallInverse
open Erdos524.FiniteSmallBallStrict

theorem inverseRadius_antitone : AntitoneOn inverseRadius (Ioi 0) := by
  intro s hs t ht hst
  apply le_of_not_gt
  intro h
  have hf := smallBallReal_strictMono (inverseRadius_spec hs).1.le (inverseRadius_spec ht).1.le h
  rw [(inverseRadius_spec hs).2, (inverseRadius_spec ht).2] at hf
  exact (not_lt_of_ge (Real.exp_le_exp.mpr (by linarith))) hf

theorem eventually_inverseLog_le_linear {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, inverseLog t ≤ ε * t := by
  let C := 3 * Real.pi ^ 2
  have hC : 0 < C := by unfold C; positivity
  let R := max 1 (C / ε ^ 3)
  filter_upwards [eventually_inverse_cubic_bounds, eventually_ge_atTop R] with t hb ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have htC : C / ε ^ 3 ≤ t := (le_max_right _ _).trans ht
  have hCbound : C ≤ t * ε ^ 3 := (div_le_iff₀ (pow_pos heps 3)).mp htC
  have ht2 : t ≤ t ^ 2 := by nlinarith
  have hlarge := mul_le_mul_of_nonneg_right ht2 (pow_nonneg heps.le 3)
  have hlarge' := mul_le_mul_of_nonneg_right (hCbound.trans hlarge) (show 0 ≤ t by linarith)
  have hcube : (inverseLog t) ^ 3 ≤ (ε * t) ^ 3 := by
    dsimp only [C] at hlarge'
    nlinarith only [hb.2.2, hlarge']
  exact (pow_le_pow_iff_left₀ hb.1.le (by positivity : 0 ≤ ε * t) (by decide : (3 : ℕ) ≠ 0)).mp hcube

theorem eventually_inverseRadius_exp_lower {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, Real.exp (-ε * t) ≤ inverseRadius t := by
  filter_upwards [eventually_inverseLog_le_linear heps, eventually_gt_atTop (0 : ℝ)] with t h ht
  rw [← exp_neg_inverseLog ht]
  exact Real.exp_le_exp.mpr (by linarith)

theorem eventually_inverseRadius_bounded_shift {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, |s - t| ≤ 1 →
      (1 - ε) * inverseRadius t ≤ inverseRadius s ∧
      inverseRadius s ≤ (1 + ε) * inverseRadius t := by
  obtain ⟨c, hc, hm⟩ := eventually_inverse_sqrt_margins heps heps2
  have hgrowth : Tendsto (fun t : ℝ ↦ c * Real.sqrt t) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 Real.tendsto_sqrt_atTop
  filter_upwards [hm, hgrowth.eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (2 : ℝ)] with t h htC ht
  intro s hst
  have hst' := abs_le.mp hst
  have hs : 0 < s := by linarith [hst'.1]
  have htp : 0 < t := by linarith
  have hδ := (inverseRadius_spec htp).1
  have hminus : 0 < 1 - ε := by linarith
  have hsδ := (inverseRadius_spec hs).1
  constructor
  · apply le_of_not_gt
    intro hh
    have hf := smallBallReal_strictMono hsδ.le (show 0 ≤ (1 - ε) * inverseRadius t by positivity) hh
    rw [(inverseRadius_spec hs).2] at hf
    have hex : Real.exp (-t - c * Real.sqrt t) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith [hst'.2])
    exact (not_lt_of_ge (h.2.trans hex)) hf
  · apply le_of_not_gt
    intro hh
    have hf := smallBallReal_strictMono (show 0 ≤ (1 + ε) * inverseRadius t by positivity) hsδ.le hh
    rw [(inverseRadius_spec hs).2] at hf
    have hex : Real.exp (-s) ≤ Real.exp (-t + c * Real.sqrt t) := Real.exp_le_exp.mpr (by linarith [hst'.1])
    exact (not_lt_of_ge (hex.trans h.1)) hf

end Erdos524.InverseSmallBallMargins
