import Erdos524.AdaptiveDyadicMesh

/-! Uniform degree/logarithm bounds over each even dyadic band. -/

namespace Erdos524.DyadicMesh

open Filter

theorem band_log_bounds {k N : ℕ} (hlo : 2 * 2 ^ k ≤ N) (hhi : N ≤ 4 * 2 ^ k) :
    (k + 2 : ℝ) / 4 ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ k + 2 := by
  have hbase : (0 : ℝ) < (2 * 2 ^ k : ℕ) := by positivity
  have hloR : ((2 * 2 ^ k : ℕ) : ℝ) ≤ N := by exact_mod_cast hlo
  have hhiR : (N : ℝ) ≤ (4 * 2 ^ k : ℕ) := by exact_mod_cast hhi
  have hNp : (0 : ℝ) < N := hbase.trans_le hloR
  have hl := Real.log_le_log hbase hloR
  have hu := Real.log_le_log hNp hhiR
  push_cast at hl hu
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ k ≠ 0), Real.log_pow] at hl
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ k ≠ 0), Real.log_pow,
    show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hu2 : Real.log 2 ≤ 1 := by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hlow := mul_le_mul_of_nonneg_left hl2 hk
  have hupp := mul_le_mul_of_nonneg_left hu2 hk
  constructor <;> nlinarith

theorem base_tendsto_atTop : Tendsto (fun k : ℕ ↦ 2 * 2 ^ k) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [eventually_ge_atTop (max N 2)] with k hk
  have hk2 : 2 ≤ k := (le_max_right _ _).trans hk
  have hkN : N ≤ k := (le_max_left _ _).trans hk
  have hp := Erdos524.AdaptiveDyadicMesh.index_le_two_pow hk2
  omega

theorem eventually_loglog_band_lower :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 2 * 2 ^ k ≤ N → N ≤ 4 * 2 ^ k →
      Real.log (k + 2 : ℝ) / 2 ≤ Real.log (Real.log (N : ℝ)) := by
  filter_upwards [Erdos524.AdaptiveDyadicMesh.log_index_tendsto.eventually_ge_atTop (4 : ℝ)] with k hk
  intro N hlo hhi
  have hb := band_log_bounds hlo hhi
  have hJp : (0 : ℝ) < k + 2 := by positivity
  have hlog := Real.log_le_log (show 0 < (k + 2 : ℝ) / 4 by positivity) hb.1
  rw [Real.log_div hJp.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hlog
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num
    linarith
  linarith

theorem eventually_sqrt_loglog_band_lower :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 2 * 2 ^ k ≤ N → N ≤ 4 * 2 ^ k →
      Real.sqrt (Real.log (k + 2 : ℝ)) / 2 ≤ Real.sqrt (Real.log (Real.log (N : ℝ))) := by
  filter_upwards [eventually_loglog_band_lower] with k hk
  intro N hlo hhi
  have h := hk N hlo hhi
  have hlog0 : 0 ≤ Real.log (k + 2 : ℝ) := Real.log_nonneg (by have hh : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)
  have hloglog0 : 0 ≤ Real.log (Real.log (N : ℝ)) := by linarith
  nlinarith [Real.sq_sqrt hlog0, Real.sq_sqrt hloglog0,
    Real.sqrt_nonneg (Real.log (k + 2 : ℝ)), Real.sqrt_nonneg (Real.log (Real.log (N : ℝ)))]

end Erdos524.DyadicMesh
