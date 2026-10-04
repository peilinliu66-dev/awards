import Erdos524.DyadicMesh
import Erdos524.PowerScaleComparisons
import Mathlib.Analysis.Real.Pi.Bounds

/-! The even dyadic mesh with exp((log k)^(2/5)) subdivisions. -/

namespace Erdos524.AdaptiveDyadicMesh

open Filter
open Erdos524.PowerScaleComparisons

noncomputable def exponent (k : ℕ) : ℝ := (Real.log (k + 2 : ℝ)) ^ (2 / 5 : ℝ)
noncomputable def count (k : ℕ) : ℕ := ⌈Real.exp (exponent k)⌉₊
noncomputable def point (k j : ℕ) : ℕ := Erdos524.DyadicMesh.point k (count k) j

theorem count_pos (k : ℕ) : 0 < count k := by
  apply Nat.ceil_pos.mpr
  exact Real.exp_pos _

theorem exponent_nonneg (k : ℕ) : 0 ≤ exponent k := by
  unfold exponent
  exact Real.rpow_nonneg (Real.log_nonneg (by have h : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith)) _

theorem count_bounds (k : ℕ) :
    Real.exp (exponent k) ≤ (count k : ℝ) ∧ (count k : ℝ) ≤ 2 * Real.exp (exponent k) := by
  have hlo := Nat.le_ceil (Real.exp (exponent k))
  have hhi := Nat.ceil_lt_add_one (Real.exp_pos (exponent k)).le
  have hone := Real.one_le_exp_iff.mpr (exponent_nonneg k)
  exact ⟨hlo, by change (⌈Real.exp (exponent k)⌉₊ : ℝ) ≤ _; linarith⟩

theorem log_index_tendsto : Tendsto (fun k : ℕ ↦ Real.log (k + 2 : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem exponent_tendsto : Tendsto exponent atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp log_index_tendsto

theorem count_real_tendsto : Tendsto (fun k ↦ (count k : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun k ↦ (count_bounds k).1) (Real.tendsto_exp_atTop.comp exponent_tendsto)

theorem eventually_exponent_le_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, exponent k ≤ c * Real.sqrt (Real.log (k + 2 : ℝ)) := by
  have h := log_index_tendsto.eventually (eventually_rpow_le_mul_rpow
    (a := 2 / 5) (b := 1 / 2) (by norm_num) hc)
  simpa only [Real.sqrt_eq_rpow, exponent] using h

theorem eventually_count_le_index : ∀ᶠ k : ℕ in atTop, count k ≤ k + 2 := by
  have h := log_index_tendsto.eventually (eventually_rpow_le_mul_rpow
    (a := 2 / 5) (b := 1) (c := 1 / 2) (by norm_num) (by norm_num))
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with k hk hk2
  rw [Real.rpow_one] at hk
  have hkp : (0 : ℝ) < k + 2 := by positivity
  have hks : (4 : ℝ) ≤ k + 2 := by exact_mod_cast (show 4 ≤ k + 2 by omega)
  have hs := Real.sq_sqrt hkp.le
  have hroot : Real.sqrt (k + 2 : ℝ) + 1 ≤ k + 2 := by nlinarith [Real.sqrt_nonneg (k + 2 : ℝ)]
  have hex : Real.exp (exponent k) ≤ Real.sqrt (k + 2 : ℝ) := by
    have he := Real.exp_le_exp.mpr hk
    rw [show (1 / 2 : ℝ) * Real.log (k + 2 : ℝ) = Real.log (k + 2 : ℝ) / 2 by ring,
      ← Erdos524.CauchyKernel.sqrt_exp_half, Real.exp_log hkp] at he
    exact he
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos (exponent k)).le
  have hb : (count k : ℝ) ≤ k + 2 := by unfold count; linarith
  exact_mod_cast hb

theorem index_le_two_pow {k : ℕ} (hk : 2 ≤ k) : k + 2 ≤ 2 ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => norm_num
  | succ j ih =>
    rw [show 2 + (j + 1) = (2 + j) + 1 by omega, pow_succ]
    omega

theorem eventually_count_le_dyadic : ∀ᶠ k : ℕ in atTop, count k ≤ 2 ^ k := by
  filter_upwards [eventually_count_le_index, eventually_ge_atTop (2 : ℕ)] with k h hk
  exact h.trans (index_le_two_pow hk)

theorem point_even (k j : ℕ) : Even (point k j) := Erdos524.DyadicMesh.point_even _ _ _
theorem point_lower (k j : ℕ) : 2 * 2 ^ k ≤ point k j := Erdos524.DyadicMesh.point_lower _ _ _

theorem point_upper (k j : ℕ) (hj : j ≤ count k) : point k j ≤ 4 * 2 ^ k := by
  have h := Erdos524.DyadicMesh.point_monotone k (count k) hj
  rw [Erdos524.DyadicMesh.point_end _ _ (count_pos k)] at h
  exact h

end Erdos524.AdaptiveDyadicMesh
