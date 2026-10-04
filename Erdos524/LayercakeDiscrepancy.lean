import Erdos524.LayercakeComparison

namespace Erdos524.LayercakeDiscrepancy
open Set MeasureTheory Filter

variable {α : Type*} [MeasurableSpace α]

theorem level_mass_integrable (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (H : ℝ) :
    IntegrableOn (fun t : ℝ => μ.real {x | t≤f x}) (Ioc 0 H) := by
  have ha : Antitone (fun t : ℝ => μ.real {x | t≤f x}) := by
    intro s t hst
    exact measureReal_mono (fun x hx => hst.trans hx)
  apply Integrable.of_bound ha.measurable.aestronglyMeasurable (μ.real univ)
  apply Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_mono (subset_univ _)

theorem integral_discrepancy_of_level_bound (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f)
    {H D : ℝ} (hH : 0≤H) (hD : 0≤D)
    (hf0 : ∀ x, 0≤f x) (hfH : ∀ x, f x≤H)
    (hlevels : ∀ t ∈ Ioc 0 H, |μ.real {x | t≤f x}-ν.real {x | t≤f x}|≤D) :
    |(∫ x, f x ∂μ)-(∫ x, f x ∂ν)|≤D*H := by
  have hnorm : ∀ x, ‖f x‖≤H := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact hfH x
  have hm : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable H (Eventually.of_forall hnorm)
  have hn : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable H (Eventually.of_forall hnorm)
  rw [hm.integral_eq_integral_Ioc_meas_le (Eventually.of_forall hf0) (Eventually.of_forall hfH),
    hn.integral_eq_integral_Ioc_meas_le (Eventually.of_forall hf0) (Eventually.of_forall hfH),
    ← integral_sub (level_mass_integrable μ f H) (level_mass_integrable ν f H)]
  have hb : ∀ᵐ t : ℝ ∂volume.restrict (Ioc 0 H),
      ‖μ.real {x | t≤f x}-ν.real {x | t≤f x}‖≤D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hlevels t ht
  have he := norm_integral_le_of_norm_le_const hb
  simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hH] using he

end Erdos524.LayercakeDiscrepancy
