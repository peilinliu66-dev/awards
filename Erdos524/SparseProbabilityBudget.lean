import Erdos524.FactorialSparseMesh

/-! Uniform harmonic lower bounds for the independent factorial blocks. -/

namespace Erdos524.FactorialSparseMesh

open Filter

theorem eventually_sparse_harmonic_budget {c a D : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 ≤ D) :
    ∀ᶠ J : ℝ in atTop, ∀ z : ℝ, J / 2 ≤ z → z ≤ 4 * J * Real.log J →
      1 / J ≤ Real.exp (c * Real.sqrt (Real.log z)) / z - D * Real.exp (-a * z) := by
  have hc4 : 0 < c ^ 4 := pow_pos hc 4
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  filter_upwards [eventually_ge_atTop (max 4 (8 * D / a ^ 2)),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 4 (3072 / c ^ 4))] with J hJ hlog
  have hJ4 : 4 ≤ J := (le_max_left _ _).trans hJ
  have hJp : 0 < J := by linarith
  have hlog4 : 4 ≤ Real.log J := (le_max_left _ _).trans hlog
  have hlog0 : 0 ≤ Real.log J := by linarith
  have hcL : 3072 ≤ c ^ 4 * Real.log J := by
    have h := (le_max_right _ _).trans hlog
    have hh := (div_le_iff₀ hc4).mp h
    nlinarith
  have hDJ : 8 * D ≤ J * a ^ 2 := (div_le_iff₀ ha2).mp ((le_max_right _ _).trans hJ)
  intro z hzlo hzhi
  have hzp : 0 < z := by linarith
  have hlogz := Real.log_le_log (show 0 < J / 2 by positivity) hzlo
  rw [Real.log_div hJp.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogz
  have hlog2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hlogzh : Real.log J / 2 ≤ Real.log z := by linarith
  have hzlog0 : 0 ≤ Real.log z := by linarith
  have hroot : Real.sqrt (Real.log J) / 2 ≤ Real.sqrt (Real.log z) := by
    have h1 := Real.sq_sqrt hlog0
    have h2 := Real.sq_sqrt hzlog0
    nlinarith [Real.sqrt_nonneg (Real.log J), Real.sqrt_nonneg (Real.log z)]
  have he4 := Real.pow_div_factorial_le_exp (c / 2 * Real.sqrt (Real.log J)) (by positivity) 4
  norm_num at he4
  have hroot4 : (Real.sqrt (Real.log J)) ^ 4 = (Real.log J) ^ 2 := by
    nlinarith [Real.sq_sqrt hlog0]
  have hm := mul_le_mul_of_nonneg_right hcL hlog0
  have hexp : 8 * Real.log J ≤ Real.exp (c / 2 * Real.sqrt (Real.log J)) := by
    rw [mul_pow, div_pow] at he4
    norm_num at he4
    rw [hroot4] at he4
    nlinarith only [he4, hm]
  have hexp' : 8 * Real.log J ≤ Real.exp (c * Real.sqrt (Real.log z)) :=
    hexp.trans (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hroot hc.le]))
  have hmain : 2 / J ≤ Real.exp (c * Real.sqrt (Real.log z)) / z := by
    apply (le_div_iff₀ hzp).mpr
    apply le_trans _ hexp'
    rw [div_mul_eq_mul_div, div_le_iff₀ hJp]
    nlinarith only [hzhi]
  have he2 := Real.pow_div_factorial_le_exp (a * J / 2) (by positivity) 2
  norm_num at he2
  have hmul := mul_le_mul_of_nonneg_right hDJ hJp.le
  have heDJ : D * J ≤ Real.exp (a * J / 2) := by nlinarith only [he2, hmul]
  have herr : D * Real.exp (-a * z) ≤ 1 / J := by
    calc
      _ ≤ D * Real.exp (-(a * J / 2)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
        nlinarith only [mul_le_mul_of_nonneg_left hzlo ha.le]
      _ ≤ 1 / J := by
        rw [Real.exp_neg, ← div_eq_mul_inv]
        apply (div_le_div_iff₀ (Real.exp_pos _) hJp).mpr
        simpa only [one_mul] using heDJ
  rw [show 2 / J = 2 * (1 / J) by ring] at hmain
  linarith only [hmain, herr]

end Erdos524.FactorialSparseMesh
