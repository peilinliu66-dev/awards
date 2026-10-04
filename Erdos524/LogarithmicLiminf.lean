import Erdos524.InverseScaleAsymptotic
import Erdos524.ConstantTermInverseLiminf

/-! The sharp logarithmic lower-envelope constant derived from the exact inverse theorem. -/

namespace Erdos524.LogarithmicLiminf

open Set Filter MeasureTheory
open Erdos524.InversePolynomialScale Erdos524.RandomPolynomialModel

theorem log_liminf_of_half_twice (X : ℕ → ℝ)
    (hl : ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) * normalizer (N : ℝ) ≤ X N)
    (hu : ∃ᶠ N : ℕ in atTop, X N ≤ 2 * normalizer (N : ℝ)) :
    liminf (fun N : ℕ ↦ Real.log (X N / Real.sqrt (N : ℝ)) / logarithmicScale (N : ℝ)) atTop =
      -logarithmicConstant := by
  let v := fun N : ℕ ↦ Real.log (X N / Real.sqrt (N : ℝ)) / logarithmicScale (N : ℝ)
  let lo := fun N : ℕ ↦ Real.log ((1 / 2 : ℝ) * delta (N : ℝ)) / logarithmicScale (N : ℝ)
  let hi := fun N : ℕ ↦ Real.log (2 * delta (N : ℝ)) / logarithmicScale (N : ℝ)
  have hlo : Tendsto lo atTop (nhds (-logarithmicConstant)) :=
    (log_multiple_delta_asymptotic (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have hhi : Tendsto hi atTop (nhds (-logarithmicConstant)) :=
    (log_multiple_delta_asymptotic (by norm_num : (0 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hproper : ∀ᶠ N : ℕ in atTop, 0 < Real.sqrt (N : ℝ) ∧ 0 < delta (N : ℝ) ∧ 0 < logarithmicScale (N : ℝ) := by
    have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [hlog.eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (1 : ℕ)] with N hx hN
    refine ⟨Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN), delta_pos hx, ?_⟩
    exact Real.rpow_pos_of_pos (Real.log_pos hx) _
  have hlow : ∀ᶠ N : ℕ in atTop, lo N ≤ v N ∧ 0 < X N / Real.sqrt (N : ℝ) := by
    filter_upwards [hl, hproper] with N hN hP
    have hratio : (1 / 2 : ℝ) * delta (N : ℝ) ≤ X N / Real.sqrt (N : ℝ) := by
      apply (le_div_iff₀ hP.1).mpr
      unfold normalizer at hN
      nlinarith only [hN]
    refine ⟨div_le_div_of_nonneg_right (Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hP.2.1) hratio) hP.2.2.le,
      lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hP.2.1) hratio⟩
  have hhigh : ∃ᶠ N : ℕ in atTop, v N ≤ hi N := by
    apply ((hu.and_eventually hproper).and_eventually hlow).mono
    intro N hN
    have hratio : X N / Real.sqrt (N : ℝ) ≤ 2 * delta (N : ℝ) := by
      apply (div_le_iff₀ hN.1.2.1).mpr
      have hh := hN.1.1
      unfold normalizer at hh
      nlinarith only [hh]
    exact div_le_div_of_nonneg_right (Real.log_le_log hN.2.2 hratio) hN.1.2.2.2.le
  have hlower (ε : ℝ) (heps : 0 < ε) : ∀ᶠ N : ℕ in atTop, -logarithmicConstant - ε ≤ v N := by
    filter_upwards [hlow, (tendsto_order.mp hlo).1 (-logarithmicConstant - ε) (by linarith)] with N hN hloN
    exact hloN.le.trans hN.1
  have hupper (ε : ℝ) (heps : 0 < ε) : ∃ᶠ N : ℕ in atTop, v N ≤ -logarithmicConstant + ε := by
    exact (hhigh.and_eventually ((tendsto_order.mp hhi).2 (-logarithmicConstant + ε) (by linarith))).mono
      (fun N hN ↦ hN.1.trans hN.2.le)
  have hb : IsBoundedUnder (fun x y : ℝ ↦ y ≤ x) atTop v := ⟨-logarithmicConstant - 1, hlower 1 (by norm_num)⟩
  have hcb : IsCoboundedUnder (fun x y : ℝ ↦ y ≤ x) atTop v := IsCoboundedUnder.of_frequently_le (hupper 1 (by norm_num))
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε heps
    exact liminf_le_of_frequently_le (hupper ε heps) hb
  · apply le_of_forall_pos_sub_le
    intro ε heps
    exact le_liminf_of_le hcb (hlower ε heps)

theorem ae_logarithmic_liminf :
    ∀ᵐ ω ∂P, liminf (fun N : ℕ ↦ Real.log (fullNorm ω N / Real.sqrt (N : ℝ)) /
      (Real.log (Real.log (N : ℝ))) ^ (1 / 3 : ℝ)) atTop = -(3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ) := by
  filter_upwards [Erdos524.InverseLiminfLower.ae_eventual_full_large (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2),
    Erdos524.InverseLiminfUpper.ae_frequent_full_small (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2)] with ω hl hu
  apply log_liminf_of_half_twice (fullNorm ω)
  · exact hl.mono (fun N hN ↦ by have hb := normalizer_nonneg (N : ℝ); nlinarith)
  · exact hu.mono (fun N hN ↦ by have hb := normalizer_nonneg (N : ℝ); nlinarith)

theorem ae_constant_logarithmic_liminf :
    ∀ᵐ ω ∂P, liminf (fun N : ℕ ↦ Real.log (withConstantNorm ω N / Real.sqrt (N : ℝ)) /
      (Real.log (Real.log (N : ℝ))) ^ (1 / 3 : ℝ)) atTop = -(3 * Real.pi ^ 2 / 4) ^ (1 / 3 : ℝ) := by
  have hl := Erdos524.InverseLiminfLower.ae_eventual_full_large (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  rw [← shift_law] at hl
  have hl' := ae_of_ae_map measurable_shift.aemeasurable hl
  have hu := Erdos524.InverseLiminfUpper.ae_frequent_full_small (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2)
  rw [← shift_law] at hu
  have hu' := ae_of_ae_map measurable_shift.aemeasurable hu
  filter_upwards [hl', hu', ae_withConstantNorm_difference] with ω hl hu hd
  apply log_liminf_of_half_twice (withConstantNorm ω)
  · filter_upwards [hl, normalizer_nat_tendsto_atTop.eventually_ge_atTop (4 : ℝ)] with N hN hb
    have hh := (abs_le.mp (hd N)).1
    nlinarith
  · apply (hu.and_eventually (normalizer_nat_tendsto_atTop.eventually_ge_atTop (4 : ℝ))).mono
    intro N hN
    have hh := (abs_le.mp (hd N)).2
    nlinarith [hN.1, hN.2]

end Erdos524.LogarithmicLiminf
