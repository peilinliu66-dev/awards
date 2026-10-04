import Erdos524.PolynomialComparisonError

/-! Threshold shifts are negligible relative to the exact inverse-small-ball radius. -/

namespace Erdos524.PolynomialComparisonParameters

open Filter
open Erdos524.InversePolynomialScale

theorem inverse_sqrt_le_tolerance {N : ℕ} (hN : 1 ≤ N) :
    1 / Real.sqrt (N : ℝ) ≤ tolerance N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hs : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) := by
    have h := Erdos524.CauchyKernel.sqrt_exp_half (Real.log (N : ℝ))
    rwa [Real.exp_log hNp] at h
  rw [hs, one_div, ← Real.exp_neg]
  exact Real.exp_le_exp.mpr (by linarith)

theorem eventually_tolerance_le_delta {α : ℝ} (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, tolerance N ≤ α * delta (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ) / 32) atTop atTop := by
    have h := (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 32)).2 hlog
    convert h using 1
    funext N
    ring
  have he : Tendsto (fun N : ℕ ↦ Real.exp (-Real.log (N : ℝ) / 32)) atTop (nhds 0) := by
    convert Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hg) using 1
    funext N
    congr 1
    dsimp only [Function.comp_def]
    ring
  have hsmall := (tendsto_order.mp he).2 α hα
  have hδ := tendsto_natCast_atTop_atTop.eventually (eventually_delta_subpower (by norm_num : (0 : ℝ) < 1 / 32))
  filter_upwards [hsmall, hδ] with N hsmall hδ
  have heq : tolerance N = Real.exp (-Real.log (N : ℝ) / 32) * Real.exp (-Real.log (N : ℝ) / 32) := by
    rw [← Real.exp_add]
    unfold tolerance
    congr 1
    ring
  rw [heq]
  have hδ' : Real.exp (-Real.log (N : ℝ) / 32) ≤ delta (N : ℝ) := by convert hδ using 1 <;> congr 1 <;> ring
  exact mul_le_mul hsmall.le hδ' (Real.exp_pos _).le hα.le

end Erdos524.PolynomialComparisonParameters
