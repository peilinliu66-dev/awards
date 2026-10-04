import Erdos524.PolynomialComparisonParameters

/-! The concrete finite-CDF error is bounded by a fixed multiple of N^(-1/16). -/

namespace Erdos524.PolynomialComparisonParameters

open Filter
open scoped BigOperators
open Erdos524.PolynomialGridCover

noncomputable def comparisonError (N : ℕ) (C : ℝ) : ℝ :=
  (75 / 6 : ℝ) * C * (softBudget N) ^ 3 / ((tolerance N) ^ 4 * (N : ℝ)) +
    8 * (∑ j : Fin (gridCount N (cutoffRange N)), (gridParameter N (cutoffRange N) j) ^ 2) /
      ((N : ℝ) ^ 2 * (tolerance N) ^ 2) + 18 / (tolerance N * Real.sqrt (cutoffRange N))

theorem comparison_error_bound {N : ℕ} (hN : 1 ≤ N) {C : ℝ} (hC : 0 ≤ C) :
    comparisonError N C ≤
      51200 * C * (Real.log (N : ℝ) + 1) ^ 3 * Real.exp (-3 * Real.log (N : ℝ) / 4) +
        96 * Real.exp (-Real.log (N : ℝ) / 8) + 18 * Real.exp (-Real.log (N : ℝ) / 16) := by
  let X := Real.log (N : ℝ)
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hNe : (N : ℝ) = Real.exp X := (Real.exp_log hNp).symm
  have hη : 0 < tolerance N := Real.exp_pos _
  have hT : 0 < cutoffRange N := Real.exp_pos _
  have hη4 : (tolerance N) ^ 4 = Real.exp (-X / 4) := by
    unfold tolerance
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [X]
    norm_num
    ring
  have hη2 : (tolerance N) ^ 2 = Real.exp (-X / 8) := by
    unfold tolerance
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [X]
    norm_num
    ring
  have hT3 : (cutoffRange N) ^ 3 = Real.exp (3 * X / 4) := by
    unfold cutoffRange
    rw [← Real.exp_nat_mul]
    congr 1
    dsimp only [X]
    norm_num
    ring
  have hd4 : (tolerance N) ^ 4 * (N : ℝ) = Real.exp (3 * X / 4) := by
    rw [hη4, hNe, ← Real.exp_add]
    congr 1
    ring
  have hd2 : (N : ℝ) * (tolerance N) ^ 2 = Real.exp (7 * X / 8) := by
    rw [hη2, hNe, ← Real.exp_add]
    congr 1
    ring
  have htail : tolerance N * Real.sqrt (cutoffRange N) = Real.exp (X / 16) := by
    unfold tolerance cutoffRange
    rw [Erdos524.CauchyKernel.sqrt_exp_half, ← Real.exp_add]
    congr 1
    dsimp only [X]
    ring
  have hsmooth : (75 / 6 : ℝ) * C * (softBudget N) ^ 3 / ((tolerance N) ^ 4 * (N : ℝ)) =
      51200 * C * (X + 1) ^ 3 * Real.exp (-3 * X / 4) := by
    rw [hd4]
    unfold softBudget
    rw [div_eq_mul_inv, ← Real.exp_neg]
    dsimp only [X]
    ring
  have hkernel : 8 * (∑ j : Fin (gridCount N (cutoffRange N)), (gridParameter N (cutoffRange N) j) ^ 2) /
      ((N : ℝ) ^ 2 * (tolerance N) ^ 2) ≤ 96 * Real.exp (-X / 8) := by
    calc
      _ ≤ 8 * (12 * (N : ℝ) * (cutoffRange N) ^ 3) / ((N : ℝ) ^ 2 * (tolerance N) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (grid_square_sum_bound hN) (by norm_num)
      _ = 96 * (cutoffRange N) ^ 3 / ((N : ℝ) * (tolerance N) ^ 2) := by field_simp; ring
      _ = 96 * Real.exp (-X / 8) := by
        rw [hT3, hd2, mul_div_assoc, ← Real.exp_sub]
        congr 2
        ring
  have ht : 18 / (tolerance N * Real.sqrt (cutoffRange N)) = 18 * Real.exp (-X / 16) := by
    rw [htail, div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  unfold comparisonError
  rw [hsmooth, ht]
  exact add_le_add (add_le_add le_rfl hkernel) le_rfl

theorem eventually_shifted_cube_le_exp :
    ∀ᶠ X : ℝ in atTop, (X + 1) ^ 3 ≤ Real.exp (X / 2) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop 3 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 8)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with X hX h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ X ^ 3),
    abs_of_pos (Real.exp_pos _)] at hX
  have hcube : (X + 1) ^ 3 ≤ (2 * X) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have he : (1 / 2 : ℝ) * X = X / 2 := by ring
  rw [he] at hX
  nlinarith only [hX, hcube]

theorem eventually_comparison_error {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, comparisonError N C ≤
      (51200 * C + 114) * Real.exp (-Real.log (N : ℝ) / 16) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually eventually_shifted_cube_le_exp,
    eventually_ge_atTop (1 : ℕ)] with N hpoly hN
  have hX : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hb := comparison_error_bound hN hC
  have hs : 51200 * C * (Real.log (N : ℝ) + 1) ^ 3 * Real.exp (-3 * Real.log (N : ℝ) / 4) ≤
      51200 * C * Real.exp (-Real.log (N : ℝ) / 16) := by
    calc
      _ ≤ 51200 * C * Real.exp (Real.log (N : ℝ) / 2) * Real.exp (-3 * Real.log (N : ℝ) / 4) := by gcongr
      _ = 51200 * C * Real.exp (-Real.log (N : ℝ) / 4) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  have hk : Real.exp (-Real.log (N : ℝ) / 8) ≤ Real.exp (-Real.log (N : ℝ) / 16) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith only [hb, hs, hk]

end Erdos524.PolynomialComparisonParameters
