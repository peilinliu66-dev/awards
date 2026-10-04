import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Summability of the stretched-log probability reserves used by the dense mesh. -/

namespace Erdos524.StretchedLogSummability

open Filter

theorem summable_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ ↦ Real.exp (-c * Real.sqrt (k : ℝ))) := by
  have hs := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ))).mul_left (720 / c ^ 6)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  have hkp : (0 : ℝ) < k := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hk
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he := Real.pow_div_factorial_le_exp (c * Real.sqrt (k : ℝ)) (by positivity) 6
  norm_num at he
  have hpow : (Real.sqrt (k : ℝ)) ^ 6 = (k : ℝ) ^ 3 := by
    rw [show (Real.sqrt (k : ℝ)) ^ 6 = ((Real.sqrt (k : ℝ)) ^ 2) ^ 3 by ring, Real.sq_sqrt hkp.le]
  rw [mul_pow, hpow] at he
  rw [show -c * Real.sqrt (k : ℝ) = -(c * Real.sqrt (k : ℝ)) by ring, Real.exp_neg]
  have hc6 : 0 < c ^ 6 := pow_pos hc 6
  have hk3 : 0 < (k : ℝ) ^ 3 := pow_pos hkp 3
  have hpos : 0 < c ^ 6 * (k : ℝ) ^ 3 / 720 := by positivity
  have hi := one_div_le_one_div_of_le hpos he
  simp only [one_div] at hi
  calc
    _ ≤ (c ^ 6 * (k : ℝ) ^ 3 / 720)⁻¹ := hi
    _ = (720 / c ^ 6) * (1 / (k : ℝ) ^ 3) := by field_simp

theorem summable_stretched_log_harmonic {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ ↦ Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) / (k : ℝ)) := by
  let f : ℕ → ℝ := fun k ↦ Real.exp (-c * Real.sqrt (Real.log (k : ℝ))) / (k : ℝ)
  have hnonneg : ∀ k, 0 ≤ f k := by intro k; unfold f; positivity
  have hmono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hmp : (0 : ℝ) < m := by exact_mod_cast hm
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hlog := Real.log_le_log hmp hmn'
    unfold f
    apply div_le_div₀ (Real.exp_pos _).le _ hmp hmn'
    apply Real.exp_le_exp.mpr
    have hh := Real.sqrt_le_sqrt hlog
    nlinarith only [mul_le_mul_of_nonneg_left hh hc.le]
  apply (summable_condensed_iff_of_nonneg hnonneg hmono).mp
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := summable_exp_neg_sqrt (mul_pos hc (Real.sqrt_pos.mpr hlog2))
  apply hs.congr
  intro k
  dsimp only [f]
  push_cast
  rw [Real.log_pow, Real.sqrt_mul (Nat.cast_nonneg k)]
  have hp : (2 : ℝ) ^ k ≠ 0 := (pow_pos (by norm_num : (0 : ℝ) < 2) k).ne'
  field_simp

theorem summable_shifted_stretched_log_harmonic {c : ℝ} (hc : 0 < c) (s : ℕ) :
    Summable (fun k : ℕ ↦ Real.exp (-c * Real.sqrt (Real.log (k + s : ℝ))) / (k + s : ℝ)) := by
  have h := (summable_nat_add_iff s).mpr (summable_stretched_log_harmonic hc)
  simpa only [Nat.cast_add] using h

end Erdos524.StretchedLogSummability
