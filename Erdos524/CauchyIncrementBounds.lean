import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Exact scalar second-moment bounds for finite Cauchy-kernel chaining. -/

namespace Erdos524.CauchyIncrementBounds

theorem inverse_root_increment_identity (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (1 / p - 1 / q) ^ 2 -
      (1 / (2 * p ^ 2) + 1 / (2 * q ^ 2) - 2 / (p ^ 2 + q ^ 2)) =
        (p - q) ^ 4 / (2 * p ^ 2 * q ^ 2 * (p ^ 2 + q ^ 2)) := by
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hq0 : q ≠ 0 := ne_of_gt hq
  have hsum : p ^ 2 + q ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem cauchy_increment_le_inverse_root_sq {v w : ℝ} (hv : 0 < v) (hw : 0 < w) :
    1 / (2 * v) + 1 / (2 * w) - 2 / (v + w) ≤
      (1 / Real.sqrt v - 1 / Real.sqrt w) ^ 2 := by
  have h := inverse_root_increment_identity (Real.sqrt v) (Real.sqrt w)
    (Real.sqrt_pos.mpr hv) (Real.sqrt_pos.mpr hw)
  rw [Real.sq_sqrt hv.le, Real.sq_sqrt hw.le] at h
  have hn : 0 ≤ (Real.sqrt v - Real.sqrt w) ^ 4 / (2 * v * w * (v + w)) := by positivity
  linarith

end Erdos524.CauchyIncrementBounds
