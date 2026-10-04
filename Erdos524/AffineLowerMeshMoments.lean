import Erdos524.AffineQuantileMoments
import Erdos524.UpperMeshAsymptotic

/-! Exact affine lower-mesh polynomial moments and logarithmic endpoint corrections. -/

namespace Erdos524.QuantileCounting

open Set MeasureTheory Filter
open scoped BigOperators

noncomputable def lowerLeft (L : ℝ) : ℝ := -4 * Real.log L
noncomputable def lowerRight (L : ℝ) : ℝ := 2 * L + 8 * Real.log L
noncomputable def lowerIntercept (L : ℝ) : ℝ := 2 * (L + 100 * Real.log L) / Real.pi ^ 2
noncomputable def lowerSlope : ℝ := 1 / Real.pi ^ 2
noncomputable def lowerTotal (L : ℝ) : ℝ :=
  affineCDF (lowerLeft L) (lowerIntercept L) lowerSlope (lowerRight L)
abbrev LowerMesh (L : ℝ) := QuantileMesh (lowerLeft L) (lowerRight L)
  (affineCDF (lowerLeft L) (lowerIntercept L) lowerSlope) ⌊lowerTotal L⌋₊

theorem integral_affine_deficit {a b : ℝ} (hab : a ≤ b) (A B L : ℝ) :
    (∫ x in Icc a b, (A - B * x) * (L - x / 2)) =
      A * L * (b - a) - (A / 4 + B * L / 2) * (b ^ 2 - a ^ 2) +
        B / 6 * (b ^ 3 - a ^ 3) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have he : (fun x : ℝ ↦ (A - B * x) * (L - x / 2)) =
      fun x ↦ (A * L - (A / 2 + B * L) * x) + (B / 2) * x ^ 2 := by funext x; ring
  rw [he, intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  simp only [smul_eq_mul]
  norm_num
  ring

theorem lower_parameters_valid {L : ℝ} (hL : 2 ≤ L) :
    lowerLeft L < lowerRight L ∧ 0 ≤ lowerSlope ∧
      0 < lowerIntercept L - lowerSlope * lowerRight L := by
  have hlog : 0 < Real.log L := Real.log_pos (by linarith)
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  constructor
  · unfold lowerLeft lowerRight
    linarith
  constructor
  · unfold lowerSlope
    positivity
  · have he : lowerIntercept L - lowerSlope * lowerRight L = 192 * Real.log L / Real.pi ^ 2 := by
      unfold lowerIntercept lowerSlope lowerRight
      ring
    rw [he]
    positivity

theorem lower_affine_deficit_integral {L : ℝ} (hL : 2 ≤ L) :
    (∫ x in Icc (lowerLeft L) (lowerRight L),
      (lowerIntercept L - lowerSlope * x) * (L - x / 2)) =
      4 / (3 * Real.pi ^ 2) * L ^ 3 +
        (208 * L ^ 2 * Real.log L + 816 * L * (Real.log L) ^ 2 -
          2304 * (Real.log L) ^ 3) / Real.pi ^ 2 := by
  rw [integral_affine_deficit (lower_parameters_valid hL).1.le]
  unfold lowerLeft lowerRight lowerIntercept lowerSlope
  ring

theorem lowerTotal_identity (L : ℝ) :
    lowerTotal L = (2 * L ^ 2 + 408 * L * Real.log L + 2376 * (Real.log L) ^ 2) / Real.pi ^ 2 := by
  unfold lowerTotal affineCDF lowerLeft lowerRight lowerIntercept lowerSlope
  ring

theorem lower_quantile_deficit_discrepancy {L : ℝ} (hL : 2 ≤ L) (mesh : LowerMesh L) :
    |(∑ i, (L - mesh.node i / 2)) -
      (4 / (3 * Real.pi ^ 2) * L ^ 3 +
        (208 * L ^ 2 * Real.log L + 816 * L * (Real.log L) ^ 2 -
          2304 * (Real.log L) ^ 3) / Real.pi ^ 2)| ≤ L + 10 * Real.log L := by
  obtain ⟨hab, hB, hr⟩ := lower_parameters_valid hL
  have h := affine_quantile_deficit_discrepancy hab hB hr mesh L
  rw [lower_affine_deficit_integral hL] at h
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have he : (lowerRight L - lowerLeft L) / 2 + |L - lowerRight L / 2| = L + 10 * Real.log L := by
    unfold lowerRight lowerLeft
    rw [show L - (2 * L + 8 * Real.log L) / 2 = -(4 * Real.log L) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    ring
  rwa [he] at h

noncomputable def lowerMaxDensity (L : ℝ) : ℝ :=
  lowerIntercept L - lowerSlope * lowerLeft L

theorem lowerMaxDensity_identity (L : ℝ) :
    lowerMaxDensity L = (2 * L + 204 * Real.log L) / Real.pi ^ 2 := by
  unfold lowerMaxDensity lowerIntercept lowerSlope lowerLeft
  ring

theorem lower_deficit_sum_remainder {L : ℝ} (hL : 2 ≤ L) (mesh : LowerMesh L) :
    (∑ i, (L - mesh.node i / 2)) ≤
      4 / (3 * Real.pi ^ 2) * L ^ 3 + 1035 * L ^ 2 * (Real.log L + 1) := by
  have hd := (abs_le.mp (lower_quantile_deficit_discrepancy hL mesh)).2
  have hL0 : 0 ≤ L := by linarith
  have hr0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hrL : Real.log L ≤ L := Real.log_le_self hL0
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hp1 : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hrLL : Real.log L ≤ L ^ 2 := hrL.trans hLL
  have hr2 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hrL hr0) hL0
  have hratio : (208 * L ^ 2 * Real.log L + 816 * L * (Real.log L) ^ 2 -
        2304 * (Real.log L) ^ 3) / Real.pi ^ 2 ≤ 1024 * L ^ 2 * Real.log L := by
    apply (div_le_iff₀ hpi).mpr
    have hh := mul_nonneg (show 0 ≤ 1024 * L ^ 2 * Real.log L by positivity) (sub_nonneg.mpr hp1)
    nlinarith [pow_nonneg hr0 3]
  have hpos : 0 ≤ L ^ 2 * Real.log L := by positivity
  nlinarith

theorem eventually_lower_deficit_sum {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ mesh : LowerMesh L,
      (∑ i, (L - mesh.node i / 2)) ≤ (4 / (3 * Real.pi ^ 2) + ε) * L ^ 3 := by
  filter_upwards [Erdos524.CauchyKernel.eventually_log_remainder_le
    (by norm_num : (0 : ℝ) < 1035) heps, eventually_ge_atTop (2 : ℝ)] with L herr hL
  intro mesh
  have h := lower_deficit_sum_remainder hL mesh
  nlinarith

theorem eventually_lower_size_controls :
    ∀ᶠ L : ℝ in atTop, 1 ≤ lowerMaxDensity L ∧ lowerMaxDensity L ≤ L ∧
      (⌊lowerTotal L⌋₊ : ℝ) ≤ L ^ 2 ∧ 0 < ⌊lowerTotal L⌋₊ := by
  have hsmall := Real.isLittleO_log_id_atTop.bound (by norm_num : (0 : ℝ) < 1 / 1000)
  filter_upwards [hsmall, eventually_ge_atTop (max 2 (Real.pi ^ 2))] with L hlog hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLp : Real.pi ^ 2 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 ≤ L := by linarith
  have hr0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  rw [id_eq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg hL0] at hlog
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hp9 : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hmlo : 1 ≤ lowerMaxDensity L := by
    rw [lowerMaxDensity_identity, le_div_iff₀ hp]
    nlinarith
  have hmhi : lowerMaxDensity L ≤ L := by
    rw [lowerMaxDensity_identity, div_le_iff₀ hp]
    have hmul := mul_nonneg hL0 (by linarith : 0 ≤ Real.pi ^ 2 - 9)
    nlinarith
  have hsquare : (Real.log L) ^ 2 ≤ L ^ 2 / 1000000 := by
    have h := mul_nonneg (show 0 ≤ L / 1000 - Real.log L by linarith)
      (show 0 ≤ L / 1000 + Real.log L by positivity)
    nlinarith
  have hcross : L * Real.log L ≤ L ^ 2 / 1000 := by
    have h := mul_le_mul_of_nonneg_left hlog hL0
    nlinarith
  have htotalhi : lowerTotal L ≤ L ^ 2 := by
    rw [lowerTotal_identity, div_le_iff₀ hp]
    have hmul := mul_nonneg (sq_nonneg L) (by linarith : 0 ≤ Real.pi ^ 2 - 9)
    nlinarith
  have htotallo : 1 ≤ lowerTotal L := by
    rw [lowerTotal_identity, le_div_iff₀ hp]
    have hcross0 : 0 ≤ L * Real.log L := by positivity
    nlinarith [sq_nonneg (Real.log L)]
  exact ⟨hmlo, hmhi, (Nat.floor_le (by linarith : 0 ≤ lowerTotal L)).trans htotalhi,
    Nat.floor_pos.mpr htotallo⟩

end Erdos524.QuantileCounting
