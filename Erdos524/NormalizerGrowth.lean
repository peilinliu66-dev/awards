import Erdos524.InversePolynomialScale

/-! Divergence of the inverse normalization, needed for bounded coefficient/index changes. -/

namespace Erdos524.InversePolynomialScale

open Filter

theorem eventually_normalizer_lower :
    ∀ᶠ x : ℝ in atTop, Real.exp (Real.log x / 4) ≤ normalizer x := by
  filter_upwards [eventually_delta_subpower (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_gt_atTop (0 : ℝ)] with x hd hx
  have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
    have h := Erdos524.CauchyKernel.sqrt_exp_half (Real.log x)
    rwa [Real.exp_log hx] at h
  unfold normalizer
  calc
    Real.exp (Real.log x / 4) = Real.sqrt x * Real.exp (-(1 / 4 : ℝ) * Real.log x) := by
      rw [hs, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.sqrt x * delta x := mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)

theorem normalizer_tendsto_atTop : Tendsto normalizer atTop atTop := by
  have hg : Tendsto (fun x : ℝ ↦ Real.exp (Real.log x / 4)) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).2 Real.tendsto_log_atTop
    have h' := Real.tendsto_exp_atTop.comp h
    convert h' using 1
    funext x
    congr 1
    dsimp only [Function.comp_def]
    ring
  apply tendsto_atTop.2
  intro R
  filter_upwards [eventually_normalizer_lower, hg.eventually_ge_atTop R] with x hx hR
  exact hR.trans hx

theorem normalizer_nat_tendsto_atTop : Tendsto (fun N : ℕ ↦ normalizer (N : ℝ)) atTop atTop :=
  normalizer_tendsto_atTop.comp tendsto_natCast_atTop_atTop

end Erdos524.InversePolynomialScale
