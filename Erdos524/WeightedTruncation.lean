import Erdos524.NearPotential
import Erdos524.AffineQuantileMeasure

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter

theorem weighted_truncated_integrable (a b A B t : ℝ) {τ M : ℝ} (hτ : 0<τ) (hM : 0≤M)
    (hr : ∀ x ∈ Icc a b, 0≤A-B*x ∧ A-B*x≤M) :
    IntegrableOn (fun x => (A-B*x)*truncatedPotential τ (x-t)) (Icc a b) := by
  have hmeas : Measurable (fun x : ℝ => (A-B*x)*truncatedPotential τ (x-t)) :=
    (measurable_const.sub (measurable_const.mul measurable_id)).mul
      ((measurable_truncatedPotential τ).comp (measurable_id.sub measurable_const))
  apply Integrable.of_bound hmeas.aestronglyMeasurable (M*logTanhPotential τ)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hp := hr x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp.1 (truncatedPotential_nonneg hτ _))]
  exact mul_le_mul hp.2 (truncatedPotential_le hτ _) (truncatedPotential_nonneg hτ _) hM

theorem weighted_truncation_gap (a b A B t : ℝ) {τ M : ℝ} (hτ : 0<τ) (hM : 0≤M)
    (hr : ∀ x ∈ Icc a b, 0≤A-B*x ∧ A-B*x≤M) :
    0≤(∫ x in Icc a b, (A-B*x)*evenPotential (x-t))-
        (∫ x in Icc a b, (A-B*x)*truncatedPotential τ (x-t)) ∧
    (∫ x in Icc a b, (A-B*x)*evenPotential (x-t))-
        (∫ x in Icc a b, (A-B*x)*truncatedPotential τ (x-t)) ≤
      2*M*(∫ x in Ioc 0 τ, logTanhPotential x) := by
  have hf := (integrable_affine_evenPotential A B t).integrableOn (s := Icc a b)
  have hg := weighted_truncated_integrable a b A B t hτ hM hr
  have hn := (nearPotential_integrable τ).comp_sub_right t
  rw [← integral_sub hf hg]
  constructor
  · apply integral_nonneg_of_ae
    have hne : ∀ᵐ x : ℝ ∂volume.restrict (Icc a b), x≠t := by
      apply ae_iff.mpr
      simpa using (measure_singleton t : (volume.restrict (Icc a b)) {t}=0)
    filter_upwards [ae_restrict_mem measurableSet_Icc,hne] with x hx hxt
    have hdiff := potential_truncation_nonneg hτ (sub_ne_zero.mpr hxt)
    have hp := mul_nonneg (hr x hx).1 hdiff
    change 0≤(A-B*x)*evenPotential (x-t)-(A-B*x)*truncatedPotential τ (x-t)
    nlinarith
  · calc
      _ ≤ ∫ x in Icc a b, M*nearPotential τ (x-t) := by
        apply integral_mono_ae (hf.sub hg) (hn.const_mul M).integrableOn
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have h1 := mul_le_mul_of_nonneg_left (potential_truncation_le_near hτ (x-t)) (hr x hx).1
        have h2 := mul_le_mul_of_nonneg_right (hr x hx).2 (nearPotential_nonneg τ (x-t))
        change (A-B*x)*evenPotential (x-t)-(A-B*x)*truncatedPotential τ (x-t)≤M*nearPotential τ (x-t)
        nlinarith
      _ ≤ ∫ x : ℝ, M*nearPotential τ (x-t) := by
        apply setIntegral_le_integral (hn.const_mul M)
        exact Eventually.of_forall (fun x => mul_nonneg hM (nearPotential_nonneg τ (x-t)))
      _ = _ := by
        rw [integral_const_mul,integral_sub_right_eq_self,integral_nearPotential]
        ring

end Erdos524.CauchyKernel
