import Erdos524.DyadicLogBounds
import Erdos524.InversePolynomialScale
import Erdos524.PowerScaleComparisons

/-! The adaptive mesh is finer than the squared inverse-small-ball radius. -/

namespace Erdos524.AdaptiveDyadicMesh

open Filter
open Erdos524.InversePolynomialScale Erdos524.InverseSmallBallMargins
open Erdos524.PowerScaleComparisons

theorem eventually_inverseLog_band :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 2 * 2 ^ k ≤ N → N ≤ 4 * 2 ^ k →
      0 < logProbability (N : ℝ) ∧ inverseLog (logProbability (N : ℝ)) ≤ exponent k / 8 := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_inverseLog_le_two_fifths (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [log_index_tendsto.eventually_ge_atTop (max 4 (2 * T + Real.log 4))] with k hk
  intro N hlo hhi
  have hb := Erdos524.DyadicMesh.band_log_bounds hlo hhi
  have hJp : (0 : ℝ) < k + 2 := by positivity
  have hz : 0 < Real.log (N : ℝ) := lt_of_lt_of_le (by positivity) hb.1
  have hl := Real.log_le_log (show 0 < (k + 2 : ℝ) / 4 by positivity) hb.1
  rw [Real.log_div hJp.ne' (by norm_num : (4 : ℝ) ≠ 0)] at hl
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num
    linarith
  have hk4 : 4 ≤ Real.log (k + 2 : ℝ) := (le_max_left _ _).trans hk
  have hkT : 2 * T + Real.log 4 ≤ Real.log (k + 2 : ℝ) := (le_max_right _ _).trans hk
  have htpos : 0 < logProbability (N : ℝ) := by unfold logProbability; linarith
  have htT : T ≤ logProbability (N : ℝ) := by unfold logProbability; linarith
  have htu : logProbability (N : ℝ) ≤ Real.log (k + 2 : ℝ) := by
    have hu := Real.log_le_log hz hb.2
    unfold logProbability
    linarith
  refine ⟨htpos, ?_⟩
  have h := hT (logProbability (N : ℝ)) htT
  have hp := Real.rpow_le_rpow htpos.le htu (by norm_num : (0 : ℝ) ≤ 2 / 5)
  unfold exponent
  linarith

theorem eventually_count_delta_sq :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 2 * 2 ^ k ≤ N → N ≤ 4 * 2 ^ k →
      Real.exp (exponent k / 2) ≤ (count k : ℝ) * (delta (N : ℝ)) ^ 2 := by
  filter_upwards [eventually_inverseLog_band] with k hk
  intro N hlo hhi
  have h := hk N hlo hhi
  have hd : delta (N : ℝ) = Real.exp (-inverseLog (logProbability (N : ℝ))) :=
    (exp_neg_inverseLog h.1).symm
  have he : Real.exp (exponent k / 2) ≤
      Real.exp (exponent k) * (delta (N : ℝ)) ^ 2 := by
    rw [hd, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
    nlinarith [exponent_nonneg k]
  exact he.trans (mul_le_mul_of_nonneg_right (count_bounds k).1 (sq_nonneg _))

theorem eventually_increment_probability_budget {a : ℝ} (ha : 0 < a) :
    ∀ᶠ k : ℕ in atTop,
      4 * (count k : ℝ) * Real.exp (-a * Real.exp (exponent k / 2)) ≤ 8 / (k + 2 : ℝ) ^ 3 := by
  have hp := log_index_tendsto.eventually (eventually_rpow_le_mul_rpow
    (a := 1) (b := 6 / 5) (c := a / 192) (by norm_num) (by positivity))
  filter_upwards [hp, log_index_tendsto.eventually_ge_atTop (1 : ℝ)] with k hp hk
  let x := Real.log (k + 2 : ℝ)
  let u := exponent k
  have hx : 0 < x := by dsimp only [x]; linarith
  have hu : 0 ≤ u := exponent_nonneg k
  have hux : u ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hk (by norm_num : (2 / 5 : ℝ) ≤ 1)
    simpa only [Real.rpow_one, u, exponent, x] using h
  rw [Real.rpow_one] at hp
  have he := Real.pow_div_factorial_le_exp (u / 2) (by positivity) 3
  norm_num at he
  have hpow : u ^ 3 = x ^ (6 / 5 : ℝ) := by
    unfold u exponent
    rw [← Real.rpow_mul_natCast hx.le]
    norm_num
  have hpower : x ≤ a / 192 * u ^ 3 := by simpa only [hpow, x] using hp
  have hlarge : 4 * x ≤ a * Real.exp (u / 2) := by
    have hh := mul_le_mul_of_nonneg_left he ha.le
    nlinarith only [hh, hpower]
  have hc := (count_bounds k).2
  have h1 : 4 * (count k : ℝ) * Real.exp (-a * Real.exp (u / 2)) ≤
      8 * Real.exp (-3 * x) := by
    calc
      _ ≤ 8 * Real.exp u * Real.exp (-a * Real.exp (u / 2)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        dsimp only [u]
        linarith
      _ = 8 * Real.exp (u - a * Real.exp (u / 2)) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
  apply h1.trans_eq
  have hJp : (0 : ℝ) < k + 2 := by positivity
  dsimp only [x]
  rw [show -3 * Real.log (k + 2 : ℝ) = -(3 * Real.log (k + 2 : ℝ)) by ring,
    Real.exp_neg, show (3 : ℝ) = (3 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hJp]
  simp only [Nat.cast_ofNat, div_eq_mul_inv]

end Erdos524.AdaptiveDyadicMesh
