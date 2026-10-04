import Erdos524.UpperEnvelopeBound

/-! Divergence and exact rescaling of the classical upper-envelope normalization. -/

namespace Erdos524.DyadicUpperScale

open Filter

theorem upperScale_tendsto_atTop : Tendsto upperScale atTop atTop := by
  have hs : Tendsto (fun N : ℕ ↦ Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.2
  intro R
  filter_upwards [hs.eventually_ge_atTop R, loglog_nat_tendsto.eventually_ge_atTop (1 : ℝ)] with N hN hlog
  apply hN.trans
  unfold upperScale
  apply Real.sqrt_le_sqrt
  have hNp : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have h := mul_le_mul_of_nonneg_left hlog hNp
  nlinarith

theorem upperScale_sqrt_two (N : ℕ) :
    upperScale N = Real.sqrt 2 * Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ))) := by
  unfold upperScale
  rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

end Erdos524.DyadicUpperScale
