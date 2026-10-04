import Erdos524.InverseRadiusStability

/-! The exact inverse-small-ball normalization as a function of polynomial degree. -/

namespace Erdos524.InversePolynomialScale

open Set Filter
open Erdos524.FiniteSmallBallInverse Erdos524.InverseSmallBallMargins

noncomputable def logProbability (x : ℝ) : ℝ := Real.log (Real.log x) / 2
noncomputable def delta (x : ℝ) : ℝ := inverseRadius (logProbability x)
noncomputable def normalizer (x : ℝ) : ℝ := Real.sqrt x * delta x

 theorem logProbability_tendsto_atTop : Tendsto logProbability atTop atTop := by
  have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).2
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop)
  change Tendsto (fun x : ℝ ↦ Real.log (Real.log x) / 2) atTop atTop
  convert h using 1
  funext x
  dsimp only [Function.comp_def]
  ring

theorem logProbability_pos {x : ℝ} (hx : 1 < Real.log x) : 0 < logProbability x := by
  unfold logProbability
  exact div_pos (Real.log_pos hx) (by norm_num)

theorem delta_pos {x : ℝ} (hx : 1 < Real.log x) : 0 < delta x :=
  (inverseRadius_spec (logProbability_pos hx)).1

theorem delta_nonneg (x : ℝ) : 0 ≤ delta x := smallBallInverse_nonneg _

theorem normalizer_nonneg (x : ℝ) : 0 ≤ normalizer x :=
  mul_nonneg (Real.sqrt_nonneg _) (delta_nonneg _)

theorem delta_exact (x : ℝ) (hx : 1 < x) :
    delta x = smallBallInverse ((Real.sqrt (Real.log x))⁻¹) := by
  unfold delta inverseRadius logProbability
  congr 1
  have hlog : 0 < Real.log x := Real.log_pos hx
  have he : Real.exp (Real.log (Real.log x) / 2) = Real.sqrt (Real.log x) := by
    rw [← Erdos524.CauchyKernel.sqrt_exp_half, Real.exp_log hlog]
  rw [show -(Real.log (Real.log x) / 2) = -(Real.log (Real.log x) / 2) from rfl,
    Real.exp_neg, he]

theorem delta_tendsto_zero : Tendsto delta atTop (nhds 0) :=
  inverseRadius_tendsto_zero.comp logProbability_tendsto_atTop

theorem delta_antitone {x y : ℝ} (hxp : 0 < x) (hx : 1 < Real.log x) (hxy : x ≤ y) : delta y ≤ delta x := by
  have hl : Real.log x ≤ Real.log y := Real.log_le_log hxp hxy
  have hy : 1 < Real.log y := hx.trans_le hl
  apply inverseRadius_antitone (logProbability_pos hx) (logProbability_pos hy)
  unfold logProbability
  exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith) hl) (by norm_num)

theorem eventually_delta_subpower {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-ε * Real.log x) ≤ delta x := by
  have hlog := Real.isLittleO_log_id_atTop.bound (show 0 < 2 * ε by positivity)
  have hL := logProbability_tendsto_atTop.eventually (eventually_inverseLog_le_linear (by norm_num : (0 : ℝ) < 1))
  filter_upwards [Real.tendsto_log_atTop.eventually hlog, hL,
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with x hlog hL hx
  have hl0 : 0 ≤ Real.log (Real.log x) := (Real.log_pos hx).le
  rw [id_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
    abs_of_nonneg (by linarith : 0 ≤ Real.log x)] at hlog
  have hp := logProbability_pos hx
  change _ ≤ inverseRadius (logProbability x)
  rw [← exp_neg_inverseLog hp]
  apply Real.exp_le_exp.mpr
  dsimp only [logProbability] at hL ⊢
  nlinarith

end Erdos524.InversePolynomialScale
