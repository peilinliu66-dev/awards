import Erdos524.InverseSmallBallMargins
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Elementary eventual comparisons between positive real powers. -/

namespace Erdos524.PowerScaleComparisons

open Filter

theorem eventually_rpow_le_mul_rpow {a b c : ℝ} (hab : a < b) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x ^ a ≤ c * x ^ b := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop (1 / c)
  filter_upwards [hg, eventually_gt_atTop (0 : ℝ)] with x hx hxp
  have h := (div_le_iff₀ hc).mp hx
  calc
    x ^ a = x ^ a * 1 := by ring
    _ ≤ x ^ a * (c * x ^ (b - a)) := mul_le_mul_of_nonneg_left (by nlinarith only [h]) (Real.rpow_nonneg hxp.le _)
    _ = c * x ^ b := by
      rw [show x ^ a * (c * x ^ (b - a)) = c * (x ^ a * x ^ (b - a)) by ring,
        ← Real.rpow_add hxp]
      congr 2
      ring

theorem eventually_inverseLog_le_two_fifths {c : ℝ} (hc : 0 < c) :
    ∀ᶠ t : ℝ in atTop, Erdos524.InverseSmallBallMargins.inverseLog t ≤ c * t ^ (2 / 5 : ℝ) := by
  let C := 3 * Real.pi ^ 2
  have hC : 0 < C := by unfold C; positivity
  have hg := eventually_rpow_le_mul_rpow (a := 1) (b := 6 / 5)
    (by norm_num) (show 0 < c ^ 3 / C by positivity)
  filter_upwards [hg, Erdos524.InverseSmallBallMargins.eventually_inverse_cubic_bounds,
    eventually_gt_atTop (0 : ℝ)] with t hg hb ht
  rw [Real.rpow_one] at hg
  have hm := mul_le_mul_of_nonneg_left hg hC.le
  have he : C * (c ^ 3 / C * t ^ (6 / 5 : ℝ)) = c ^ 3 * t ^ (6 / 5 : ℝ) := by field_simp
  rw [he] at hm
  have hcub : (Erdos524.InverseSmallBallMargins.inverseLog t) ^ 3 ≤ (c * t ^ (2 / 5 : ℝ)) ^ 3 := by
    have hr : t ^ (6 / 5 : ℝ) = (t ^ (2 / 5 : ℝ)) ^ 3 := by
      rw [← Real.rpow_mul_natCast ht.le]
      norm_num
    rw [mul_pow, ← hr]
    exact hb.2.2.trans hm
  exact (pow_le_pow_iff_left₀ hb.1.le (by positivity : 0 ≤ c * t ^ (2 / 5 : ℝ)) (by decide : (3 : ℕ) ≠ 0)).mp hcub

end Erdos524.PowerScaleComparisons
