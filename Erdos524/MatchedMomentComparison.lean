import Erdos524.FourthOrderTaylor
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Erdos524.MatchedMomentComparison
open MeasureTheory Filter
open Erdos524.FourthOrderTaylor

 theorem cubicTaylor_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hpow : ∀ k : ℕ, k≤3 → Integrable (fun t : ℝ => t^k) μ) : Integrable (cubicTaylor f) μ := by
  have h1 : Integrable (fun t : ℝ => t) μ := by simpa only [pow_one] using hpow 1 (by decide)
  have hi1 := h1.const_mul (deriv f 0)
  have hi2 := ((hpow 2 (by decide)).const_mul (iteratedDeriv 2 f 0)).div_const 2
  have hi3 := ((hpow 3 (by decide)).const_mul (iteratedDeriv 3 f 0)).div_const 6
  exact (((integrable_const (f 0)).add hi1).add hi2).add hi3

theorem integral_cubicTaylor (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hpow : ∀ k : ℕ, k≤3 → Integrable (fun t : ℝ => t^k) μ) :
    (∫ t, cubicTaylor f t ∂μ) = f 0+deriv f 0*(∫ t : ℝ, t ∂μ)+
      iteratedDeriv 2 f 0*(∫ t : ℝ, t^2 ∂μ)/2+
      iteratedDeriv 3 f 0*(∫ t : ℝ, t^3 ∂μ)/6 := by
  have h1 : Integrable (fun t : ℝ => t) μ := by simpa only [pow_one] using hpow 1 (by decide)
  have hi1 := h1.const_mul (deriv f 0)
  have hi2 := ((hpow 2 (by decide)).const_mul (iteratedDeriv 2 f 0)).div_const 2
  have hi3 := ((hpow 3 (by decide)).const_mul (iteratedDeriv 3 f 0)).div_const 6
  unfold cubicTaylor
  rw [integral_add (f := fun t : ℝ => f 0+deriv f 0*t+iteratedDeriv 2 f 0*t^2/2)
      (g := fun t : ℝ => iteratedDeriv 3 f 0*t^3/6) (((integrable_const (f 0)).add hi1).add hi2) hi3,
    integral_add (f := fun t : ℝ => f 0+deriv f 0*t) (g := fun t : ℝ => iteratedDeriv 2 f 0*t^2/2)
      ((integrable_const (f 0)).add hi1) hi2,
    integral_add (f := fun _ : ℝ => f 0) (g := fun t : ℝ => deriv f 0*t) (integrable_const (f 0)) hi1,
    integral_div,integral_div,integral_const_mul,integral_const_mul,integral_const_mul]
  simp

theorem integral_remainder_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) (hfi : Integrable f μ)
    (hpow : ∀ k : ℕ, k≤4 → Integrable (fun t : ℝ => t^k) μ)
    {M : ℝ} (hM : ∀ t : ℝ, |iteratedDeriv 4 f t|≤M) :
    |∫ t, f t-cubicTaylor f t ∂μ|≤(M/24)*(∫ t : ℝ, t^4 ∂μ) := by
  have hp := cubicTaylor_integrable μ f (fun k hk => hpow k (by omega))
  have hmajor := ((hpow 4 (by decide)).const_mul M).div_const 24
  have he : (∫ t, ‖f t-cubicTaylor f t‖ ∂μ)≤∫ t : ℝ, M*t^4/24 ∂μ := by
    apply integral_mono_ae (hfi.sub hp).norm hmajor
    apply Eventually.of_forall
    intro t
    have h := cubic_remainder_bound hf hM t
    simpa only [Real.norm_eq_abs,Pi.sub_apply,(show Even 4 by decide).pow_abs] using h
  have hn := norm_integral_le_integral_norm (fun t => f t-cubicTaylor f t) (μ := μ)
  rw [Real.norm_eq_abs] at hn
  rw [integral_div,integral_const_mul] at he
  calc
    _ ≤ _ := hn.trans he
    _ = _ := by ring

theorem integral_compare_three_moments (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) (hfμ : Integrable f μ) (hfν : Integrable f ν)
    (hμ : ∀ k : ℕ, k≤4 → Integrable (fun t : ℝ => t^k) μ)
    (hν : ∀ k : ℕ, k≤4 → Integrable (fun t : ℝ => t^k) ν)
    (hmatch : ∀ k : ℕ, k≤3 → (∫ t : ℝ, t^k ∂μ)=(∫ t : ℝ, t^k ∂ν))
    {M : ℝ} (hM : ∀ t : ℝ, |iteratedDeriv 4 f t|≤M) :
    |(∫ t, f t ∂μ)-(∫ t, f t ∂ν)|≤
      (M/24)*((∫ t : ℝ, t^4 ∂μ)+(∫ t : ℝ, t^4 ∂ν)) := by
  have hμ3 : ∀ k : ℕ, k≤3 → Integrable (fun t : ℝ => t^k) μ := fun k hk => hμ k (by omega)
  have hν3 : ∀ k : ℕ, k≤3 → Integrable (fun t : ℝ => t^k) ν := fun k hk => hν k (by omega)
  have hpμ := cubicTaylor_integrable μ f hμ3
  have hpν := cubicTaylor_integrable ν f hν3
  have hp : (∫ t, cubicTaylor f t ∂μ)=(∫ t, cubicTaylor f t ∂ν) := by
    rw [integral_cubicTaylor μ f hμ3,integral_cubicTaylor ν f hν3]
    have h1 := hmatch 1 (by decide)
    simp only [pow_one] at h1
    rw [h1,hmatch 2 (by decide),hmatch 3 (by decide)]
  have heq : (∫ t, f t ∂μ)-(∫ t, f t ∂ν)=
      (∫ t, f t-cubicTaylor f t ∂μ)-(∫ t, f t-cubicTaylor f t ∂ν) := by
    rw [integral_sub hfμ hpμ,integral_sub hfν hpν,hp]
    ring
  rw [heq]
  have h1 := integral_remainder_bound μ hf hfμ hμ hM
  have h2 := integral_remainder_bound ν hf hfν hν hM
  have h := abs_sub (∫ t, f t-cubicTaylor f t ∂μ) (∫ t, f t-cubicTaylor f t ∂ν)
  nlinarith

end Erdos524.MatchedMomentComparison
