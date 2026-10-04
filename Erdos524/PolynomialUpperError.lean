import Erdos524.PolynomialFullUpper
import Erdos524.PolynomialTolerance

/-! Polynomial decay of the additional Gaussian grid/tail comparison errors. -/

namespace Erdos524.PolynomialComparisonParameters

open Filter

noncomputable def upperGridError (N : ℕ) (r : ℝ) : ℝ :=
  2 * (Real.sqrt (2 * (Real.exp 1) ^ 2 / (N : ℝ)) / tolerance N +
    Real.exp 1 / ((r + 4 * tolerance N) *
      Real.sqrt ((⌈cutoffRange N * (N : ℝ)⌉₊ : ℝ) / (N : ℝ) + 1)))

noncomputable def upperGridConstant : ℝ := 2 * Real.sqrt (2 * (Real.exp 1) ^ 2) + 2 * Real.exp 1

theorem inverse_sqrt_le_tolerance_sq {N : ℕ} (hN : 1 ≤ N) :
    1 / Real.sqrt (N : ℝ) ≤ (tolerance N) ^ 2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hs : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) := by
    have h := Erdos524.CauchyKernel.sqrt_exp_half (Real.log (N : ℝ))
    rwa [Real.exp_log hNp] at h
  rw [hs, one_div, ← Real.exp_neg]
  unfold tolerance
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  norm_num
  linarith

theorem inverse_tolerance_sqrtRange (N : ℕ) :
    1 / (tolerance N * Real.sqrt (cutoffRange N)) = tolerance N := by
  unfold tolerance cutoffRange
  rw [Erdos524.CauchyKernel.sqrt_exp_half, ← Real.exp_add, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem upperGridError_bound {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (hr : 0 ≤ r) :
    upperGridError N r ≤ upperGridConstant * tolerance N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN
  have hη : 0 < tolerance N := Real.exp_pos _
  have hT : 0 < cutoffRange N := Real.exp_pos _
  have hfirst : Real.sqrt (2 * (Real.exp 1) ^ 2 / (N : ℝ)) / tolerance N ≤
      Real.sqrt (2 * (Real.exp 1) ^ 2) * tolerance N := by
    rw [Real.sqrt_div (by positivity)]
    calc
      _ = (Real.sqrt (2 * (Real.exp 1) ^ 2) * (1 / Real.sqrt (N : ℝ))) / tolerance N := by ring
      _ ≤ (Real.sqrt (2 * (Real.exp 1) ^ 2) * (tolerance N) ^ 2) / tolerance N := by
        apply div_le_div_of_nonneg_right _ hη.le
        exact mul_le_mul_of_nonneg_left (inverse_sqrt_le_tolerance_sq hN) (Real.sqrt_nonneg _)
      _ = _ := by field_simp
  have hceil := Nat.le_ceil (cutoffRange N * (N : ℝ))
  have hpoint : cutoffRange N ≤ (⌈cutoffRange N * (N : ℝ)⌉₊ : ℝ) / (N : ℝ) + 1 := by
    have hh := (le_div_iff₀ hNp).mpr hceil
    linarith
  have hden : tolerance N * Real.sqrt (cutoffRange N) ≤
      (r + 4 * tolerance N) * Real.sqrt ((⌈cutoffRange N * (N : ℝ)⌉₊ : ℝ) / (N : ℝ) + 1) := by
    exact mul_le_mul (by linarith) (Real.sqrt_le_sqrt hpoint) (Real.sqrt_nonneg _) (by positivity)
  have hsecond : Real.exp 1 / ((r + 4 * tolerance N) *
      Real.sqrt ((⌈cutoffRange N * (N : ℝ)⌉₊ : ℝ) / (N : ℝ) + 1)) ≤ Real.exp 1 * tolerance N := by
    calc
      _ ≤ Real.exp 1 / (tolerance N * Real.sqrt (cutoffRange N)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le (mul_pos hη (Real.sqrt_pos.mpr hT)) hden
      _ = _ := by rw [div_eq_mul_one_div, inverse_tolerance_sqrtRange]
  unfold upperGridError upperGridConstant
  nlinarith only [hfirst, hsecond]

end Erdos524.PolynomialComparisonParameters
