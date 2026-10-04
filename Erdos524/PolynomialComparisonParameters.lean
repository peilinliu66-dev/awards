import Erdos524.PolynomialFullProbability
import Erdos524.InversePolynomialScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Explicit finite-comparison parameters and polynomially decaying scalar errors. -/

namespace Erdos524.PolynomialComparisonParameters

open Filter MeasureTheory
open scoped BigOperators
open Erdos524.PolynomialGridCover

noncomputable def cutoffRange (N : ℕ) : ℝ := Real.exp (Real.log (N : ℝ) / 4)
noncomputable def tolerance (N : ℕ) : ℝ := Real.exp (-Real.log (N : ℝ) / 16)
noncomputable def softBudget (N : ℕ) : ℝ := 16 * (Real.log (N : ℝ) + 1)

theorem parameter_controls {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ cutoffRange N ∧ cutoffRange N ≤ N ∧ 0 < tolerance N ∧ 1 ≤ softBudget N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  refine ⟨Real.one_le_exp_iff.mpr (by positivity), ?_, Real.exp_pos _, ?_⟩
  · unfold cutoffRange
    exact (Real.exp_le_exp.mpr (show Real.log (N : ℝ) / 4 ≤ Real.log (N : ℝ) by linarith)).trans_eq (Real.exp_log hNp)
  · unfold softBudget
    linarith

theorem grid_count_bound {N : ℕ} (hN : 1 ≤ N) :
    (gridCount N (cutoffRange N) : ℝ) ≤ 3 * (N : ℝ) * cutoffRange N := by
  have hc := (parameter_controls hN).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hprod : 1 ≤ cutoffRange N * (N : ℝ) := one_le_mul_of_one_le_of_one_le hc hN1
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ cutoffRange N * (N : ℝ) by positivity)
  unfold gridCount
  push_cast
  nlinarith

theorem grid_parameter_bound {N : ℕ} (hN : 1 ≤ N) (j : Fin (gridCount N (cutoffRange N))) :
    0 ≤ gridParameter N (cutoffRange N) j ∧ gridParameter N (cutoffRange N) j ≤ 2 * cutoffRange N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hT := (parameter_controls hN).1
  have hj : (j : ℝ) ≤ (⌈cutoffRange N * (N : ℝ)⌉₊ : ℝ) := by
    exact_mod_cast (show j.val ≤ ⌈cutoffRange N * (N : ℝ)⌉₊ by have hh := j.isLt; unfold gridCount at hh; omega)
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ cutoffRange N * (N : ℝ) by positivity)
  unfold gridParameter
  constructor
  · positivity
  · apply (div_le_iff₀ hNp).mpr
    have hm := mul_nonneg (sub_nonneg.mpr hN1) (show 0 ≤ cutoffRange N by linarith)
    nlinarith

theorem grid_square_sum_bound {N : ℕ} (hN : 1 ≤ N) :
    (∑ j : Fin (gridCount N (cutoffRange N)), (gridParameter N (cutoffRange N) j) ^ 2) ≤
      12 * (N : ℝ) * (cutoffRange N) ^ 3 := by
  have hterm (j : Fin (gridCount N (cutoffRange N))) :
      (gridParameter N (cutoffRange N) j) ^ 2 ≤ 4 * (cutoffRange N) ^ 2 := by
    have h := grid_parameter_bound hN j
    have hT := (parameter_controls hN).1
    nlinarith [mul_nonneg h.1 (show 0 ≤ 2 * cutoffRange N by linarith)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ hterm j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hc := mul_le_mul_of_nonneg_right (grid_count_bound hN) (show 0 ≤ 4 * (cutoffRange N) ^ 2 by positivity)
  nlinarith only [hs, hc]

theorem softBudget_log {N : ℕ} (hN : 1 ≤ N) :
    Real.log ((gridCount N (cutoffRange N) + gridCount N (cutoffRange N)) +
      (gridCount N (cutoffRange N) + gridCount N (cutoffRange N)) : ℕ) ≤ softBudget N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hT : 0 < cutoffRange N := Real.exp_pos _
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hcount : (0 : ℝ) < gridCount N (cutoffRange N) := by unfold gridCount; positivity
  have hcountbound := grid_count_bound hN
  have h := Real.log_le_log (show 0 < 4 * (gridCount N (cutoffRange N) : ℝ) by positivity)
    (show 4 * (gridCount N (cutoffRange N) : ℝ) ≤ 12 * (N : ℝ) * cutoffRange N by nlinarith)
  rw [Real.log_mul (mul_pos (by norm_num) hNp).ne' hT.ne',
    Real.log_mul (by norm_num : (12 : ℝ) ≠ 0) hNp.ne'] at h
  have hlogT : Real.log (cutoffRange N) = Real.log (N : ℝ) / 4 := Real.log_exp _
  rw [hlogT] at h
  have h12 : Real.log 12 ≤ 11 := by have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 12); linarith
  have he : (((gridCount N (cutoffRange N) + gridCount N (cutoffRange N)) +
      (gridCount N (cutoffRange N) + gridCount N (cutoffRange N)) : ℕ) : ℝ) =
      4 * (gridCount N (cutoffRange N) : ℝ) := by push_cast; ring
  rw [he]
  unfold softBudget
  linarith

end Erdos524.PolynomialComparisonParameters
