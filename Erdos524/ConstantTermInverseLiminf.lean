import Erdos524.PolynomialConstantTerm
import Erdos524.InverseLiminf

/-! The exact inverse liminf is unchanged by the original independent constant coefficient. -/

namespace Erdos524.ConstantTermInverseLiminf

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.RandomPolynomialModel Erdos524.InversePolynomialScale
open Erdos524.FiniteSmallBallInverse

theorem bounded_difference_ratio_close (u v : ℕ → ℝ) (h : ∀ n, |v n - u n| ≤ 1)
    {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, |v N / normalizer (N : ℝ) - u N / normalizer (N : ℝ)| ≤ ε := by
  filter_upwards [normalizer_nat_tendsto_atTop.eventually_ge_atTop (max 1 (1 / ε))] with N hN
  have hB : 0 < normalizer (N : ℝ) := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hN)
  have hBε : 1 ≤ ε * normalizer (N : ℝ) := by
    have hh := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hN)
    nlinarith
  rw [← sub_div, abs_div, abs_of_pos hB]
  apply (div_le_div_of_nonneg_right (h N) hB.le).trans
  exact (div_le_iff₀ hB).mpr hBε

theorem ae_constant_inverse_liminf_eq_one :
    ∀ᵐ ω ∂P, liminf (fun N ↦ withConstantNorm ω N / normalizer (N : ℝ)) atTop = 1 := by
  have hl := Erdos524.InverseLiminfLower.ae_eventual_ratio_all_positive_slack
  rw [← shift_law] at hl
  have hl' := ae_of_ae_map measurable_shift.aemeasurable hl
  have hu := Erdos524.InverseLiminfUpper.ae_frequent_ratio_all_positive_slack
  rw [← shift_law] at hu
  have hu' := ae_of_ae_map measurable_shift.aemeasurable hu
  filter_upwards [hl', hu', ae_withConstantNorm_difference] with ω hl hu hd
  have hclose (ε : ℝ) (heps : 0 < ε) :=
    bounded_difference_ratio_close (fun N ↦ fullNorm (shift ω) N) (withConstantNorm ω) hd heps
  have hlarge : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      1 - ε ≤ withConstantNorm ω N / normalizer (N : ℝ) := by
    intro ε heps
    filter_upwards [hl (ε / 2) (by linarith), hclose (ε / 2) (by linarith)] with N hN hc
    have h := (abs_le.mp hc).1
    linarith
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop,
      withConstantNorm ω N / normalizer (N : ℝ) ≤ 1 + ε := by
    intro ε heps
    apply ((hu (ε / 2) (by linarith)).and_eventually (hclose (ε / 2) (by linarith))).mono
    intro N hN
    have h := (abs_le.mp hN.2).2
    linarith [hN.1]
  have hbounded : IsBoundedUnder (fun x y : ℝ ↦ y ≤ x) atTop
      (fun N ↦ withConstantNorm ω N / normalizer (N : ℝ)) :=
    isBoundedUnder_of ⟨0, fun N ↦ div_nonneg (withConstantNorm_nonneg ω N) (normalizer_nonneg _)⟩
  have hcobounded : IsCoboundedUnder (fun x y : ℝ ↦ y ≤ x) atTop
      (fun N ↦ withConstantNorm ω N / normalizer (N : ℝ)) :=
    IsCoboundedUnder.of_frequently_le (hsmall 1 (by norm_num))
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε heps
    exact liminf_le_of_frequently_le (hsmall ε heps) hbounded
  · apply le_of_forall_pos_sub_le
    intro ε heps
    exact le_liminf_of_le hcobounded (hlarge ε heps)

theorem ae_constant_explicit_inverse_liminf_eq_one :
    ∀ᵐ ω ∂P, liminf (fun N : ℕ ↦ withConstantNorm ω N /
      (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) atTop = 1 := by
  filter_upwards [ae_constant_inverse_liminf_eq_one] with ω hω
  have he : (fun N : ℕ ↦ withConstantNorm ω N / normalizer (N : ℝ)) =ᶠ[atTop]
      (fun N : ℕ ↦ withConstantNorm ω N / (Real.sqrt (N : ℝ) * smallBallInverse ((Real.sqrt (Real.log (N : ℝ)))⁻¹))) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    unfold normalizer
    rw [delta_exact _ (by exact_mod_cast (show 1 < N by omega))]
  rwa [liminf_congr he] at hω

end Erdos524.ConstantTermInverseLiminf
