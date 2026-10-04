import Erdos524.SampleBoxLowerExponent
import Erdos524.AffineLowerMeshMoments

/-! Scalar asymptotics for the sample-box lower bound, including its factor one-half. -/

namespace Erdos524.SampleBoxAsymptotic

open Filter
open Erdos524.CauchyKernel

noncomputable def sampleNormalization : ℝ :=
  (3 / 2 : ℝ) * Real.log 2 - Real.log (Real.sqrt (2 * Real.pi))

noncomputable def sampleContribution (L N D : ℝ) : ℝ :=
  -D / 2 - N * (200 * Real.log L) - (15 * L ^ 2 * (Real.log L + 1)) / 2 +
    N * sampleNormalization - N ^ 2 * Real.exp (-160 * Real.log L) - Real.log 2

noncomputable def sampleRemainderConstant : ℝ :=
  210 + |sampleNormalization| + |Real.log 2|

theorem sample_energy_cost_le_one {L N : ℝ} (hL : 2 ≤ L) (hN : 0 ≤ N) (hNmax : N ≤ L ^ 2) :
    N ^ 2 * Real.exp (-160 * Real.log L) ≤ 1 := by
  have hlpos : 0 < L := by linarith
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsq : N ^ 2 ≤ L ^ 4 := by
    have h := mul_nonneg (sub_nonneg.mpr hNmax) (show 0 ≤ L ^ 2 + N by positivity)
    nlinarith
  have he4 : Real.exp (4 * Real.log L) = L ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log hlpos]
  calc
    _ ≤ N ^ 2 * Real.exp (-(4 * Real.log L)) := by
      gcongr
      linarith
    _ ≤ 1 := by
      rw [Real.exp_neg, he4, ← div_eq_mul_inv, div_le_one (pow_pos hlpos 4)]
      exact hsq

theorem sampleContribution_remainder {L N D : ℝ}
    (hL : 2 ≤ L) (hN : 0 ≤ N) (hNmax : N ≤ L ^ 2) :
    -D / 2 - sampleRemainderConstant * L ^ 2 * (Real.log L + 1) ≤ sampleContribution L N D := by
  have hlog : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hNH := mul_le_mul_of_nonneg_right hNmax (show 0 ≤ 200 * Real.log L by positivity)
  have hnorm : -(L ^ 2 * |sampleNormalization|) ≤ N * sampleNormalization := by
    have h1 := mul_le_mul_of_nonneg_left (neg_abs_le sampleNormalization) hN
    have h2 := mul_le_mul_of_nonneg_right hNmax (abs_nonneg sampleNormalization)
    nlinarith
  have henergy := sample_energy_cost_le_one hL hN hNmax
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hnormpad := mul_nonneg (abs_nonneg sampleNormalization) (show 0 ≤ L ^ 2 * Real.log L by positivity)
  have hlogpad := mul_nonneg (abs_nonneg (Real.log 2))
    (show 0 ≤ L ^ 2 * (Real.log L + 1) - 1 by nlinarith)
  have hlog2 := le_abs_self (Real.log 2)
  unfold sampleRemainderConstant sampleContribution
  nlinarith

theorem eventually_sampleContribution_lower {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ L : ℝ in atTop, ∀ N D : ℝ, 0 ≤ N → N ≤ L ^ 2 →
      D ≤ (4 / (3 * Real.pi ^ 2) + ε) * L ^ 3 →
      -(2 / (3 * Real.pi ^ 2) + ε) * L ^ 3 ≤ sampleContribution L N D := by
  have hC : 0 < sampleRemainderConstant := by unfold sampleRemainderConstant; positivity
  filter_upwards [eventually_log_remainder_le hC (by linarith : 0 < ε / 2),
    eventually_ge_atTop (2 : ℝ)] with L herr hL
  intro N D hN hNmax hD
  have h := sampleContribution_remainder (D := D) hL hN hNmax
  have he : 4 / (3 * Real.pi ^ 2) = 2 * (2 / (3 * Real.pi ^ 2)) := by ring
  rw [he] at hD
  nlinarith

end Erdos524.SampleBoxAsymptotic
