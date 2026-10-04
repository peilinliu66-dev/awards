import Erdos524.SparseProbabilityBudget
import Mathlib.Analysis.PSeries

/-! The probability lower budget on actual even factorial blocks dominates a harmonic series. -/

namespace Erdos524.FactorialSparseMesh

open Filter MeasureTheory
open scoped ENNReal

theorem endpoint_log_lower (j : ℕ) : (j : ℝ) ≤ Real.log (endpoint j : ℝ) := by
  have hf : 2 ^ j ≤ (j + 1).factorial := by
    simpa only [Nat.factorial_one, one_mul, Nat.one_add] using
      (Nat.factorial_mul_pow_le_factorial (m := 1) (n := j))
  have hf' : (2 : ℝ) ^ j ≤ ((j + 1).factorial : ℝ) := by exact_mod_cast hf
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) j) hf'
  rw [Real.log_pow] at hlog
  have hfac : (0 : ℝ) < (j + 1).factorial := by exact_mod_cast Nat.factorial_pos (j + 1)
  have he : Real.log (endpoint j : ℝ) = Real.log 2 + 2 * Real.log ((j + 1).factorial : ℝ) := by
    simp only [endpoint, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_pos hfac 2).ne', Real.log_pow]
  rw [he]
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (j : ℝ) by positivity)
  nlinarith

theorem blockLength_log_bounds {j : ℕ} (hj : 2 ≤ j) :
    (j + 2 : ℝ) / 2 ≤ Real.log (blockLength j : ℝ) ∧
      Real.log (blockLength j : ℝ) ≤ 4 * (j + 2 : ℝ) * Real.log (j + 2 : ℝ) := by
  have hepos : (0 : ℝ) < endpoint j := by exact_mod_cast endpoint_pos j
  have hbpos : (0 : ℝ) < blockLength j := by exact_mod_cast blockLength_pos j
  have hlo := Real.log_le_log hepos (show (endpoint j : ℝ) ≤ blockLength j by exact_mod_cast blockLength_lower j)
  have hhi := Real.log_le_log hbpos (show (blockLength j : ℝ) ≤ endpoint (j + 1) by
    exact_mod_cast (Nat.sub_le (endpoint (j + 1)) (endpoint j)))
  constructor
  · have h := (endpoint_log_lower j).trans hlo
    have hj' : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  · have h := hhi.trans (endpoint_log_upper (j + 1))
    have hJ : (2 : ℝ) ≤ j + 2 := by have hh : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
    have hl : Real.log 2 ≤ Real.log (j + 2 : ℝ) := Real.log_le_log (by norm_num) hJ
    have hl0 : 0 ≤ Real.log (j + 2 : ℝ) := Real.log_nonneg (by linarith)
    have hm := mul_nonneg (show 0 ≤ (j + 2 : ℝ) - 1 by linarith) hl0
    push_cast at h
    rw [show (j : ℝ) + 1 + 1 = j + 2 by ring] at h
    nlinarith

theorem eventually_factorial_harmonic_budget {c a D : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 ≤ D) :
    ∀ᶠ j : ℕ in atTop,
      1 / (j + 2 : ℝ) ≤
        Real.exp (c * Real.sqrt (Real.log (Real.log (blockLength j : ℝ)))) / Real.log (blockLength j : ℝ) -
          D * Real.exp (-a * Real.log (blockLength j : ℝ)) := by
  have hJ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  filter_upwards [hJ.eventually (eventually_sparse_harmonic_budget hc ha hD), eventually_ge_atTop (2 : ℕ)] with j h hj
  exact h _ (blockLength_log_bounds hj).1 (blockLength_log_bounds hj).2

theorem tsum_eq_top_of_eventual_harmonic {p : ℕ → ℝ≥0∞}
    (h : ∀ᶠ j : ℕ in atTop, ENNReal.ofReal (1 / (j + 2 : ℝ)) ≤ p j) : ∑' j, p j = ⊤ := by
  by_contra htop
  have hs := ENNReal.summable_toReal htop
  have hle : ∀ᶠ j : ℕ in atTop, 1 / (j + 2 : ℝ) ≤ (p j).toReal := by
    filter_upwards [h] with j hj
    exact (ENNReal.ofReal_le_iff_le_toReal (ENNReal.ne_top_of_tsum_ne_top htop j)).mp hj
  have hsum : Summable (fun j : ℕ ↦ 1 / (j + 2 : ℝ)) := by
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [hle] with j hj
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (j + 2 : ℝ))] using hj
  exact (Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp (by simpa using hsum)))

end Erdos524.FactorialSparseMesh
