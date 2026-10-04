import Erdos524.PolynomialConstantTerm
import Erdos524.UpperScaleGrowth
import Erdos524.UpperEnvelopeLower
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The original constant-term polynomial and the sqrt(2) upper-envelope constant. -/

namespace Erdos524.ConstantTermUpperEnvelope

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.RandomPolynomialModel Erdos524.DyadicUpperScale

 theorem bounded_difference_upper_ratio_close (u v : ℕ → ℝ) (h : ∀ n, |v n - u n| ≤ 1)
    {ε : ℝ} (heps : 0 < ε) : ∀ᶠ N : ℕ in atTop, |v N / upperScale N - u N / upperScale N| ≤ ε := by
  filter_upwards [upperScale_tendsto_atTop.eventually_ge_atTop (max 1 (1 / ε))] with N hN
  have hB : 0 < upperScale N := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hN)
  have hBε : 1 ≤ ε * upperScale N := by
    have hh := (div_le_iff₀ heps).mp ((le_max_right _ _).trans hN)
    nlinarith
  rw [← sub_div, abs_div, abs_of_pos hB]
  apply (div_le_div_of_nonneg_right (h N) hB.le).trans
  exact (div_le_iff₀ hB).mpr hBε

theorem ae_constant_upper_ratio_all_slack :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, withConstantNorm ω N / upperScale N ≤ 1 + ε := by
  have hu := Erdos524.UpperEnvelopeBound.ae_eventual_upper_ratio_all_slack
  rw [← shift_law] at hu
  have hu' := ae_of_ae_map measurable_shift.aemeasurable hu
  filter_upwards [hu', ae_withConstantNorm_difference] with ω hu hd
  intro ε heps
  filter_upwards [hu (ε / 2) (by linarith),
    bounded_difference_upper_ratio_close (fun N ↦ fullNorm (shift ω) N) (withConstantNorm ω) hd (show 0 < ε / 2 by linarith)] with N hN hc
  have hh := (abs_le.mp hc).2
  linarith

theorem ae_constant_upper_normalized_limsup_eq_one :
    ∀ᵐ ω ∂P, limsup (fun N ↦ withConstantNorm ω N / upperScale N) atTop = 1 := by
  have hcount : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ᶠ N : ℕ in atTop,
      1 - 1 / (k + 2 : ℝ) ≤ fullNorm ω N / upperScale N := by
    apply ae_all_iff.mpr
    intro k
    have hk : (1 : ℝ) < k + 2 := by have hh : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
    have hpos : 0 < 1 - 1 / (k + 2 : ℝ) := by
      have h : 1 / (k + 2 : ℝ) < 1 := (div_lt_iff₀ (by positivity : 0 < (k + 2 : ℝ))).mpr (by linarith)
      linarith
    exact Erdos524.UpperEnvelopeLower.ae_frequent_upper_ratio hpos (by have h := one_div_pos.mpr (show 0 < (k + 2 : ℝ) by positivity); linarith)
  rw [← shift_law] at hcount
  have hcount' := ae_of_ae_map measurable_shift.aemeasurable hcount
  filter_upwards [hcount', ae_constant_upper_ratio_all_slack, ae_withConstantNorm_difference] with ω hl hu hd
  have hb : IsBoundedUnder (· ≤ ·) atTop (fun N ↦ withConstantNorm ω N / upperScale N) :=
    ⟨2, by
      change ∀ᶠ N : ℕ in atTop, withConstantNorm ω N / upperScale N ≤ 2
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hu 1 (by norm_num)⟩
  have hcb : IsCoboundedUnder (· ≤ ·) atTop (fun N ↦ withConstantNorm ω N / upperScale N) :=
    isCoboundedUnder_le_of_le atTop (fun N ↦ div_nonneg (withConstantNorm_nonneg ω N) (Real.sqrt_nonneg _))
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε heps
    exact limsup_le_of_le hcb (hu ε heps)
  · apply le_of_forall_pos_le_add
    intro ε heps
    obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
    have hsmall : 2 / (k + 2 : ℝ) ≤ ε := by
      apply (div_le_iff₀ (by positivity : 0 < (k + 2 : ℝ))).mpr
      have hh := (div_lt_iff₀ heps).mp hk
      nlinarith
    have hfreq : ∃ᶠ N : ℕ in atTop, 1 - 2 / (k + 2 : ℝ) ≤ withConstantNorm ω N / upperScale N := by
      apply ((hl k).and_eventually (bounded_difference_upper_ratio_close
        (fun N ↦ fullNorm (shift ω) N) (withConstantNorm ω) hd (show 0 < 1 / (k + 2 : ℝ) by positivity))).mono
      intro N hN
      have hh := (abs_le.mp hN.2).1
      have he : 2 / (k + 2 : ℝ) = 2 * (1 / (k + 2 : ℝ)) := by ring
      rw [he]
      linarith [hN.1]
    have h := le_limsup_of_frequently_le hfreq hb
    linarith

theorem limsup_rescale_sqrt_two (X : ℕ → ℝ) (hX : ∀ N, 0 ≤ X N)
    (hb : IsBoundedUnder (· ≤ ·) atTop (fun N ↦ X N / upperScale N))
    (hlim : limsup (fun N ↦ X N / upperScale N) atTop = 1) :
    limsup (fun N : ℕ ↦ X N / Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hm : Monotone (fun x : ℝ ↦ Real.sqrt 2 * x) := fun _ _ h ↦ mul_le_mul_of_nonneg_left h hs.le
  have hcb : IsCoboundedUnder (· ≤ ·) atTop (fun N ↦ X N / upperScale N) :=
    isCoboundedUnder_le_of_le atTop (fun N ↦ div_nonneg (hX N) (Real.sqrt_nonneg _))
  have hmap := hm.map_limsup_of_continuousAt (fun N ↦ X N / upperScale N) (by fun_prop) hb hcb
  have he (N : ℕ) : Real.sqrt 2 * (X N / upperScale N) =
      X N / Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ))) := by
    rw [upperScale_sqrt_two]
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    calc
      _ = (X N * (Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ))))⁻¹) * (Real.sqrt 2 * (Real.sqrt 2)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hs.ne', mul_one]
  change Real.sqrt 2 * limsup (fun N ↦ X N / upperScale N) atTop =
    limsup (fun N ↦ Real.sqrt 2 * (X N / upperScale N)) atTop at hmap
  simp_rw [he] at hmap
  rw [hlim, mul_one] at hmap
  exact hmap.symm

theorem ae_explicit_upper_limsup_sqrt_two :
    ∀ᵐ ω ∂P, limsup (fun N : ℕ ↦ fullNorm ω N /
      Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2 := by
  filter_upwards [Erdos524.UpperEnvelopeLower.ae_upper_normalized_limsup_eq_one,
    Erdos524.UpperEnvelopeBound.ae_eventual_upper_ratio (by norm_num : (0 : ℝ) < 1)] with ω hlim hb
  exact limsup_rescale_sqrt_two (fullNorm ω) (fullNorm_nonneg ω) ⟨2, by
    change ∀ᶠ N : ℕ in atTop, fullNorm ω N / upperScale N ≤ 2
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hb⟩ hlim

theorem ae_constant_explicit_upper_limsup_sqrt_two :
    ∀ᵐ ω ∂P, limsup (fun N : ℕ ↦ withConstantNorm ω N /
      Real.sqrt ((N : ℝ) * Real.log (Real.log (N : ℝ)))) atTop = Real.sqrt 2 := by
  filter_upwards [ae_constant_upper_normalized_limsup_eq_one, ae_constant_upper_ratio_all_slack] with ω hlim hb
  exact limsup_rescale_sqrt_two (withConstantNorm ω) (withConstantNorm_nonneg ω)
    ⟨2, by
      change ∀ᶠ N : ℕ in atTop, withConstantNorm ω N / upperScale N ≤ 2
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using hb 1 (by norm_num)⟩ hlim

end Erdos524.ConstantTermUpperEnvelope
