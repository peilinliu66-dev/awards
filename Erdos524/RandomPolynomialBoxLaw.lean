import Erdos524.RandomPolynomialFinite
import Erdos524.PolynomialFullProbability

/-! Identification of the finite all-interval box with the actual infinite-sign supremum event. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments Erdos524.FullPolynomialBox Erdos524.PhasePolynomialIdentity

theorem fullBox_eq_finiteNorm {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    fullBox N r = {z | finiteNorm z ≤ Real.sqrt (N : ℝ) * r} := by
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  ext z
  change (∀ x : ℝ, |x| ≤ 1 → |normalizedPolynomial N z x| ≤ r) ↔ ‖finitePolyCM z‖ ≤ Real.sqrt (N : ℝ) * r
  rw [ContinuousMap.norm_le _ (mul_nonneg hroot.le hr)]
  constructor
  · intro h x
    have hx := h x (abs_le.mpr x.property)
    unfold normalizedPolynomial at hx
    rw [abs_div, abs_of_pos hroot, div_le_iff₀ hroot] at hx
    simpa only [Real.norm_eq_abs, finitePolyCM_apply, mul_comm] using hx
  · intro h x hx
    have hb := h ⟨x, abs_le.mp hx⟩
    unfold normalizedPolynomial
    rw [abs_div, abs_of_pos hroot, div_le_iff₀ hroot]
    simpa only [Real.norm_eq_abs, finitePolyCM_apply, mul_comm] using hb

theorem fullNorm_scaled_probability {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | fullNorm ω N ≤ Real.sqrt (N : ℝ) * r} =
      (Measure.pi (fun _ : Fin N ↦ signLaw)).real (fullBox N r) := by
  unfold Measure.real
  rw [fullNorm_finite_event_law, fullBox_eq_finiteNorm hN hr]

theorem freshNorm_scaled_probability (a : ℕ) {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    P.real {ω | freshNorm a N ω ≤ Real.sqrt (N : ℝ) * r} =
      (Measure.pi (fun _ : Fin N ↦ signLaw)).real (fullBox N r) := by
  unfold Measure.real
  rw [freshNorm_event_law, fullNorm_finite_event_law, fullBox_eq_finiteNorm hN hr]

end Erdos524.RandomPolynomialModel
