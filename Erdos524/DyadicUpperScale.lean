import Mathlib.Tactic
import Erdos524.DyadicUpperProbability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos524.DyadicUpperScale
open Filter
open Erdos524.DyadicMesh Erdos524.DyadicUpperProbability

noncomputable def upperScale (N : ℕ) : ℝ := Real.sqrt (2*(N:ℝ)*Real.log (Real.log (N:ℝ)))
noncomputable def logSlack : ℝ := Real.log 2-Real.log (Real.log 2)

theorem log_band_comparison (k n : ℕ) (hn : 2*2^k≤n) :
    Real.log (k+2:ℝ)≤Real.log (Real.log (n:ℝ))+logSlack := by
  have hl2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg _
  have hbase : 2*(2:ℝ)^k≤(n:ℝ) := by exact_mod_cast hn
  have hln := Real.log_le_log (by positivity : (0:ℝ)<2*(2:ℝ)^k) hbase
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hln
  have hf : 0<(k+1:ℝ)*Real.log 2 := by positivity
  have hll := Real.log_le_log hf (show (k+1:ℝ)*Real.log 2≤Real.log (n:ℝ) by nlinarith)
  rw [Real.log_mul (by positivity) (ne_of_gt hl2)] at hll
  have hklog := Real.log_le_log (by positivity : (0:ℝ)<k+2) (show (k+2:ℝ)≤2*(k+1) by linarith)
  rw [Real.log_mul (by norm_num) (by positivity)] at hklog
  unfold logSlack
  linarith

theorem loglog_nat_tendsto : Tendsto (fun N : ℕ => Real.log (Real.log (N:ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem eventually_upperScale_pos : ∀ᶠ N : ℕ in atTop, 0<upperScale N := by
  filter_upwards [loglog_nat_tendsto.eventually_gt_atTop (0:ℝ),eventually_ge_atTop (1:ℕ)] with N hL hN
  unfold upperScale
  apply Real.sqrt_pos.mpr
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  positivity

theorem eventually_threshold_le_upperScale {c d : ℝ} (hc : 0<c) (hcd : c<d) (Q : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ j n : ℕ, point k Q j≤n → threshold c k Q j≤d*upperScale n := by
  have hd : 0<d := hc.trans hcd
  have hdiff : 0<d^2-c^2 := by nlinarith
  have hL := loglog_nat_tendsto.eventually_ge_atTop (max 1 (c^2*logSlack/(d^2-c^2)))
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp hL
  filter_upwards [eventually_ge_atTop N0] with k hk
  intro j n hn
  have hbase : 2*2^k≤n := (point_lower k Q j).trans hn
  have hkn : k≤n := by have hh := index_le_two_pow k; omega
  have hlarge := hN0 n (hk.trans hkn)
  have hpos : 0≤Real.log (Real.log (n:ℝ)) := by linarith [le_max_left (1:ℝ) (c^2*logSlack/(d^2-c^2))]
  have hpay : c^2*logSlack≤(d^2-c^2)*Real.log (Real.log (n:ℝ)) := by
    have he := (le_max_right (1:ℝ) (c^2*logSlack/(d^2-c^2))).trans hlarge
    have hh := (div_le_iff₀ hdiff).mp he
    nlinarith
  have hln := log_band_comparison k n hbase
  have hklog : 0≤Real.log (k+2:ℝ) := Real.log_nonneg (by have hh := Nat.cast_nonneg (α := ℝ) k; linarith)
  have hpoint : (0:ℝ)≤point k Q j := Nat.cast_nonneg _
  have hnp : (0:ℝ)≤n := Nat.cast_nonneg _
  have hpointN : (point k Q j:ℝ)≤n := by exact_mod_cast hn
  have hthreshold : (threshold c k Q j)^2=c^2*(2*(point k Q j:ℝ)*Real.log (k+2:ℝ)) := by
    unfold threshold
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hscale : (d*upperScale n)^2=d^2*(2*(n:ℝ)*Real.log (Real.log (n:ℝ))) := by
    unfold upperScale
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hp := mul_le_mul_of_nonneg_right hpointN hklog
  have hp' := mul_le_mul_of_nonneg_left hp (show 0≤2*c^2 by positivity)
  have hl := mul_le_mul_of_nonneg_left hln (show 0≤2*(n:ℝ)*c^2 by positivity)
  have hf := mul_le_mul_of_nonneg_left hpay (show (0:ℝ)≤2*(n:ℝ) by positivity)
  apply (sq_le_sq₀ (threshold_pos hc k Q j).le (mul_nonneg hd.le (Real.sqrt_nonneg _))).mp
  change (threshold c k Q j)^2≤(d*upperScale n)^2
  rw [hthreshold,hscale]
  nlinarith

end Erdos524.DyadicUpperScale
