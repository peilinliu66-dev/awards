import Erdos524.FiniteSmallBallIncrement

/-! Continuity away from zero, proved from uniform finite-dimensional shell and tail bounds. -/

namespace Erdos524.FiniteSmallBallContinuity

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.FiniteSmallBallBasic Erdos524.FiniteSmallBallIncrement

theorem smallBallReal_continuousAt_pos {δ : ℝ} (hδ : 0 < δ) : ContinuousAt smallBallReal δ := by
  apply Metric.continuousAt_iff.mpr
  intro ε heps
  let R := 8 * Real.exp 1 / (δ * ε)
  let T := R ^ 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hT : 0 ≤ T := sq_nonneg R
  have hspos : 0 < Real.sqrt (T + 1) := Real.sqrt_pos.mpr (by linarith)
  have hs : R ≤ Real.sqrt (T + 1) := by
    have hsq := Real.sq_sqrt (show 0 ≤ T + 1 by linarith)
    dsimp [T] at hsq
    nlinarith [Real.sqrt_nonneg (T + 1)]
  have htail0 : Real.exp 1 / ((δ / 2) * Real.sqrt (T + 1)) ≤ ε / 4 := by
    apply (div_le_iff₀ (mul_pos (by linarith) hspos)).mpr
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ δ * ε by positivity)
    have he : δ * ε * R = 8 * Real.exp 1 := by dsimp [R]; field_simp
    rw [he] at hm
    nlinarith
  have htail (r : ℝ) (hr : δ / 2 ≤ r) :
      Real.exp 1 / (r * Real.sqrt (T + 1)) ≤ ε / 4 := by
    apply le_trans _ htail0
    apply div_le_div_of_nonneg_left (Real.exp_pos 1).le (by positivity)
    exact mul_le_mul_of_nonneg_right hr hspos.le
  let η := min (δ / 2) (ε * Real.exp (-T) / 8)
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  refine ⟨η, hη, ?_⟩
  intro x hx
  have hclose : |x - δ| < η := by simpa only [Real.dist_eq] using hx
  have hhalf : |x - δ| < δ / 2 := hclose.trans_le (min_le_left _ _)
  have hxpos : 0 < x := by have h := (abs_lt.mp hhalf).1; linarith
  have hxmin : δ / 2 ≤ x := by have h := (abs_lt.mp hhalf).1; linarith
  have hnoise : 2 * |x - δ| / Real.exp (-T) ≤ ε / 4 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    have h := hclose.le.trans (min_le_right _ _)
    change |x - δ| ≤ ε * Real.exp (-T) / 8 at h
    nlinarith
  rw [Real.dist_eq, abs_lt]
  by_cases hdx : δ ≤ x
  · have hi := smallBallReal_increment hT hδ (sub_nonneg.mpr hdx)
    rw [add_sub_cancel] at hi
    have hn : 2 * (x - δ) / Real.exp (-T) ≤ ε / 4 := by
      rwa [abs_of_nonneg (sub_nonneg.mpr hdx)] at hnoise
    have hm := smallBallReal_mono hdx
    have ht := htail δ (by linarith)
    constructor <;> linarith
  · have hxd : x ≤ δ := (lt_of_not_ge hdx).le
    have hi := smallBallReal_increment hT hxpos (sub_nonneg.mpr hxd)
    rw [add_sub_cancel] at hi
    have hn : 2 * (δ - x) / Real.exp (-T) ≤ ε / 4 := by
      simpa only [abs_of_nonpos (sub_nonpos.mpr hxd), neg_sub] using hnoise
    have hm := smallBallReal_mono hxd
    have ht := htail x hxmin
    constructor <;> linarith

end Erdos524.FiniteSmallBallContinuity
