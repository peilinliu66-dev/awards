import Mathlib.MeasureTheory.Integral.Layercake

/-!
The elementary integration step for the finite Anderson argument.
The level-set comparison is an explicit hypothesis of this general integration
lemma; its geometric proof is supplied separately in the application.
-/

namespace Erdos524.LayercakeComparison

open Set MeasureTheory Filter
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

theorem setLIntegral_le_of_superlevel_inter_le (μ : Measure α)
    {f : α → ℝ} (hf : Measurable f) (hnonneg : ∀ x, 0 ≤ f x)
    (S T : Set α)
    (hlevels : ∀ t : ℝ, 0 < t →
      μ ({x | t ≤ f x} ∩ S) ≤ μ ({x | t ≤ f x} ∩ T)) :
    ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x in T, ENNReal.ofReal (f x) ∂μ := by
  rw [lintegral_eq_lintegral_meas_le (μ.restrict S)
      (Eventually.of_forall hnonneg) hf.aemeasurable,
    lintegral_eq_lintegral_meas_le (μ.restrict T)
      (Eventually.of_forall hnonneg) hf.aemeasurable]
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hm : MeasurableSet {x | t ≤ f x} := measurableSet_le measurable_const hf
  rw [Measure.restrict_apply hm, Measure.restrict_apply hm]
  exact hlevels t ht

end Erdos524.LayercakeComparison
