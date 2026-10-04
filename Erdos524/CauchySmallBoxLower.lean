import Erdos524.CauchyResidualBounds
import Erdos524.GaussianBoxDensity

/-! A finite independent sample-box/residual bridge for small-ball lower bounds. -/

namespace Erdos524.CauchySmallBoxLower

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal BigOperators
open Erdos524.CauchyKernel Erdos524.CauchyGaussianRegression Erdos524.GaussianBoxDensity

variable {n m : ℕ}

theorem half_le_probability_norm_lt {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {R : Ω → (Fin m → ℝ)}
    (hm : Measurable R) (hR : Integrable R P) {η : ℝ} (hη : 0 < η)
    (hmean : (∫ z, ‖R z‖ ∂P) ≤ η / 2) :
    (1 / 2 : ℝ≥0∞) ≤ P {z | ‖R z‖ < η} := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun z ↦ norm_nonneg (R z)))
    hR.norm η
  have hb : P.real {z | η ≤ ‖R z‖} ≤ 1 / 2 := by nlinarith
  have hb' : P {z | η ≤ ‖R z‖} ≤ (1 / 2 : ℝ≥0∞) := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by norm_num)).mp
    simpa only [measureReal_def, ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using hb
  have he : {z | ‖R z‖ < η} = {z | η ≤ ‖R z‖}ᶜ := by ext z; simp
  rw [he, prob_compl_eq_one_sub (measurableSet_le measurable_const hm.norm)]
  have hsub := tsub_le_tsub_left hb' 1
  norm_num at hsub ⊢
  exact hsub

theorem small_box_lower_of_residual_budget
    (x : Fin (n + 1) → ℝ) (v : Fin (m + 1) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (hv : ∀ j, 0 < v j)
    (w : Fin (n + 1) → ℝ) {δ η : ℝ} (hη : 0 < η)
    (hweights : ∀ j, (∑ i, |weights x v j i| * w i) ≤ δ - η)
    (hresidual : (∫ z, ‖cauchyResidual x v z‖ ∂jointMeasure x v) ≤ η / 2) :
    (1 / 2 : ℝ≥0∞) * (multivariateGaussian 0 (cauchy x)) (ofLp ⁻¹' box w) ≤
      (multivariateGaussian 0 (cauchy v)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
  haveI := (joint_gaussian x v).isProbabilityMeasure
  have hmeas : Measurable (cauchyResidual x v) := by
    unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual sample evaluation
    fun_prop
  have hg := half_le_probability_norm_lt hmeas (residual_gaussian x v).integrable hη hresidual
  have hs : (jointMeasure x v) (sample ⁻¹' box w) =
      (multivariateGaussian 0 (cauchy x)) (ofLp ⁻¹' box w) := by
    have h := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ (box w)) (sample_law x v hx hv)
    rw [Measure.map_apply (by unfold sample; fun_prop) (measurableSet_box w),
      Measure.map_apply (by fun_prop) (measurableSet_box w)] at h
    exact h
  have heval : (jointMeasure x v) (evaluation ⁻¹' box (fun _ ↦ δ)) =
      (multivariateGaussian 0 (cauchy v)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
    have h := congrArg (fun μ : Measure (Fin (m + 1) → ℝ) ↦ μ (box (fun _ ↦ δ)))
      (evaluation_law x v hx hv)
    rw [Measure.map_apply (by unfold evaluation; fun_prop) (measurableSet_box _),
      Measure.map_apply (by fun_prop) (measurableSet_box _)] at h
    exact h
  have hind := (samples_residual_independent x v hx hinj hv).measure_inter_preimage_eq_mul
    (box w) {z | ‖z‖ < η} (measurableSet_box w) (measurableSet_lt (by fun_prop) measurable_const)
  have hsub : sample ⁻¹' box w ∩ cauchyResidual x v ⁻¹' {z | ‖z‖ < η} ⊆
      evaluation ⁻¹' box (fun _ ↦ δ) := by
    intro z hz j hj
    have hw (i : Fin (n + 1)) : |sample z i| ≤ w i := abs_le.mpr (hz.1 i (Set.mem_univ i))
    have hsum : |∑ i, weights x v j i * sample z i| ≤ δ - η := calc
      _ ≤ ∑ i, |weights x v j i * sample z i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |weights x v j i| * w i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hw i) (abs_nonneg _)
      _ ≤ _ := hweights j
    have hR : |cauchyResidual x v z j| < η :=
      (show |cauchyResidual x v z j| ≤ ‖cauchyResidual x v z‖ from by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (cauchyResidual x v z) j).trans_lt hz.2
    have he : evaluation z j = cauchyResidual x v z j + ∑ i, weights x v j i * sample z i := by
      unfold cauchyResidual Erdos524.FiniteGaussianRegression.residual
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
      ring
    apply abs_le.mp
    rw [he]
    exact (abs_add_le _ _).trans (by linarith)
  rw [← hs, ← heval]
  calc
    (1 / 2 : ℝ≥0∞) * (jointMeasure x v) (sample ⁻¹' box w) ≤
        (jointMeasure x v) (sample ⁻¹' box w) *
          (jointMeasure x v) {z | ‖cauchyResidual x v z‖ < η} := by
      rw [mul_comm (1 / 2)]
      exact mul_le_mul_right hg _
    _ = (jointMeasure x v) (sample ⁻¹' box w ∩ cauchyResidual x v ⁻¹' {z | ‖z‖ < η}) := hind.symm
    _ ≤ _ := measure_mono hsub

end Erdos524.CauchySmallBoxLower
