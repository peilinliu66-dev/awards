import Erdos524.FactorialOldBound
import Erdos524.PolynomialScaleStability

/-! Deterministic scale payment for the almost-sure old-polynomial budget. -/

namespace Erdos524.FactorialSparseMesh

open Filter
open Erdos524.InversePolynomialScale

theorem endpoint_next_log_upper (j : ℕ) :
    Real.log (endpoint (j + 1) : ℝ) ≤ 4 * (j + 2 : ℝ) * Real.log (j + 2 : ℝ) := by
  have h := endpoint_log_upper (j + 1)
  push_cast at h
  rw [show (j : ℝ) + 1 + 1 = j + 2 by ring] at h
  have hJ : (2 : ℝ) ≤ j + 2 := by have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hJ
  have hl0 := Real.log_nonneg (show (1 : ℝ) ≤ j + 2 by linarith)
  have hm := mul_nonneg (show 0 ≤ (j + 2 : ℝ) - 1 by linarith) hl0
  nlinarith

theorem endpoint_next_sqrt (j : ℕ) :
    Real.sqrt (endpoint (j + 1) : ℝ) = (j + 2 : ℝ) * Real.sqrt (endpoint j : ℝ) := by
  rw [endpoint_succ]
  push_cast
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem endpoint_next_real_tendsto : Tendsto (fun j ↦ (endpoint (j + 1) : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (StrictMono.tendsto_atTop (fun i j hij ↦ endpoint_strictMono (by omega)))

theorem eventually_old_payment {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ j : ℕ in atTop, oldBudget j ≤ ε * normalizer (endpoint (j + 1) : ℝ) := by
  have hJ : Tendsto (fun j : ℕ ↦ (j : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (show 0 < ε / 8 by positivity)
  filter_upwards [hJ.eventually hlog, endpoint_next_real_tendsto.eventually eventually_delta_log_lower] with j hlog hdelta
  let J : ℝ := j + 2
  let B : ℝ := endpoint (j + 1)
  have hJp : 0 < J := by unfold J; positivity
  have hJ1 : 1 ≤ J := by unfold J; have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
  have hl0 : 0 ≤ Real.log J := Real.log_nonneg hJ1
  have hB0 : 0 ≤ Real.log B := (show 0 ≤ (j + 1 : ℝ) by positivity).trans (by simpa only [B, Nat.cast_add, Nat.cast_one] using endpoint_log_lower (j + 1))
  have hBL : Real.log B ≤ 4 * J * Real.log J := endpoint_next_log_upper j
  have hsmall : Real.log J ≤ ε / 8 * Real.sqrt J := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl0,
      abs_of_nonneg (Real.rpow_nonneg hJp.le _), ← Real.sqrt_eq_rpow] at hlog
    exact hlog
  have hsJ := Real.sq_sqrt hJp.le
  have hsL := Real.sq_sqrt hl0
  have hsB := Real.sq_sqrt hB0
  have hlog2 : (Real.log J) ^ 2 ≤ ε ^ 2 * J / 64 := by
    have hh := mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ ε / 8 * Real.sqrt J + Real.log J by positivity)
    nlinarith only [hh, hsJ]
  have hfirst := mul_le_mul_of_nonneg_left hBL (show 0 ≤ 8 * Real.log J by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hlog2 (show 0 ≤ 32 * J by positivity)
  have hprod : Real.sqrt (8 * Real.log J) * Real.sqrt (Real.log B) ≤ ε * J := by
    have hs8 := Real.sq_sqrt (show 0 ≤ 8 * Real.log J by positivity)
    have hsq : (Real.sqrt (8 * Real.log J) * Real.sqrt (Real.log B)) ^ 2 ≤ (ε * J) ^ 2 := by
      rw [mul_pow, hs8, hsB]
      nlinarith only [hfirst, hsecond, sq_nonneg (ε * J)]
    exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg heps.le hJp.le)).mp hsq
  have hbase : oldBudget j * Real.sqrt (Real.log B) ≤ ε * Real.sqrt B := by
    have hh := mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg (endpoint j : ℝ))
    rw [show Real.sqrt B = J * Real.sqrt (endpoint j : ℝ) from endpoint_next_sqrt j]
    unfold oldBudget
    change Real.sqrt (endpoint j : ℝ) * Real.sqrt (8 * Real.log J) * Real.sqrt (Real.log B) ≤ _
    nlinarith only [hh]
  have hd : 0 ≤ delta B := delta_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hdelta (oldBudget_pos j).le
  have hhigh := mul_le_mul_of_nonneg_right hbase hd
  change oldBudget j ≤ ε * (Real.sqrt B * delta B)
  change oldBudget j * 1 ≤ oldBudget j * (Real.sqrt (Real.log B) * delta B) at hlow
  nlinarith only [hlow, hhigh]

theorem blockLength_half (j : ℕ) : (endpoint (j + 1) : ℝ) / 2 ≤ blockLength j := by
  have hp : 2 ≤ (j + 2) ^ 2 := by
    have h := Nat.pow_le_pow_left (by omega : 2 ≤ j + 2) 2
    omega
  have he : 2 * endpoint j ≤ endpoint (j + 1) := by rw [endpoint_succ]; nlinarith [endpoint_pos j]
  have he' : 2 * (endpoint j : ℝ) ≤ endpoint (j + 1) := by exact_mod_cast he
  unfold blockLength
  rw [Nat.cast_sub (endpoint_strictMono.monotone (Nat.le_succ j))]
  linarith

theorem eventually_block_normalizer_le {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᶠ j : ℕ in atTop, normalizer (blockLength j : ℝ) ≤ (1 + ε) * normalizer (endpoint (j + 1) : ℝ) := by
  filter_upwards [endpoint_next_real_tendsto.eventually (eventually_half_interval_normalizer heps heps2)] with j h
  apply h _ (blockLength_half j)
  exact_mod_cast Nat.sub_le (endpoint (j + 1)) (endpoint j)

end Erdos524.FactorialSparseMesh
