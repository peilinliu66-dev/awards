import Erdos524.FiniteSmallBallBasic

/-! Uniform large-parameter and large-radius estimates for the finite-only envelope. -/

namespace Erdos524.FiniteSmallBallTail

open Set Filter MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallBasic
open Erdos524.CauchyKernel Erdos524.UnorderedGaussianBounds
open Erdos524.FiniteSmallBallLower Erdos524.GaussianBoxDensity Erdos524.LaplaceKernelComparison

theorem probability_norm_lt_lower {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {R : Ω → E}
    (hm : Measurable R) (hR : Integrable R P) {η C : ℝ} (hη : 0 < η)
    (hmean : (∫ z, ‖R z‖ ∂P) ≤ C) :
    1 - ENNReal.ofReal (C / η) ≤ P {z | ‖R z‖ < η} := by
  have h := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (fun z ↦ norm_nonneg (R z)))
    hR.norm η
  have hb : P.real {z | η ≤ ‖R z‖} ≤ C / η := (le_div_iff₀ hη).mpr (by nlinarith)
  have hb' : P {z | η ≤ ‖R z‖} ≤ ENNReal.ofReal (C / η) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P {z | η ≤ ‖R z‖})]
    exact ENNReal.ofReal_le_ofReal hb
  have he : {z | ‖R z‖ < η} = {z | η ≤ ‖R z‖}ᶜ := by ext z; simp
  rw [he, prob_compl_eq_one_sub (measurableSet_le measurable_const hm.norm)]
  exact tsub_le_tsub_left hb' 1

theorem cauchy_box_lower {n : ℕ} (v : Fin (n + 1) → ℝ)
    {V η : ℝ} (hV : 0 < V) (hv : ∀ i, V ≤ v i) (hη : 0 < η) :
    1 - ENNReal.ofReal ((1 / Real.sqrt V) / η) ≤
      (multivariateGaussian 0 (cauchy v)) (ofLp ⁻¹' box (fun _ ↦ η)) := by
  let B := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) ↦ ℝ)).toContinuousLinearMap
  have hR : Integrable (ofLp : EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ))
      (multivariateGaussian 0 (cauchy v)) := B.integrable_comp IsGaussian.integrable_id
  have h := probability_norm_lt_lower (by fun_prop) hR hη
    (integral_cauchy_sup_norm_unordered_le v hV hv)
  refine h.trans (measure_mono ?_)
  intro z hz i hi
  apply abs_le.mp
  have hc : |z i| ≤ ‖ofLp z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (ofLp z) i
  exact hc.trans hz.le

theorem finiteKernel_box_lower {n : ℕ} (u : Fin (n + 1) → ℝ)
    {U δ : ℝ} (hU : 0 ≤ U) (hu : ∀ i, U ≤ u i) (hδ : 0 < δ) :
    1 - ENNReal.ofReal (Real.exp 1 / (δ * Real.sqrt (U + 1))) ≤
      (multivariateGaussian 0 (finiteKernel u)) (ofLp ⁻¹' box (fun _ ↦ δ)) := by
  have hη : 0 < δ / Real.exp 1 := div_pos hδ (Real.exp_pos 1)
  have hc := cauchy_box_lower (fun i ↦ u i + 1) (by linarith : 0 < U + 1)
    (fun i ↦ by linarith [hu i]) hη
  have he : (1 / Real.sqrt (U + 1)) / (δ / Real.exp 1) =
      Real.exp 1 / (δ * Real.sqrt (U + 1)) := by
    simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv, one_mul]
    ring
  rw [he] at hc
  have hp := shifted_cauchy_box_le_finite u (fun i ↦ hU.trans (hu i)) (δ / Real.exp 1)
  have hs : Real.exp 1 * (δ / Real.exp 1) = δ := by field_simp
  rw [hs] at hp
  exact hc.trans hp

theorem finiteSmallBall_lower_large_radius {δ : ℝ} (hδ : 0 < δ) :
    1 - ENNReal.ofReal (Real.exp 1 / δ) ≤ finiteSmallBall δ := by
  apply le_iInf
  intro n
  apply le_iInf
  intro u
  have h := finiteKernel_box_lower (fun i ↦ (u i : ℝ)) (by norm_num : (0 : ℝ) ≤ 0)
    (fun i ↦ (u i).property) hδ
  simpa using h

theorem smallBallReal_lower_large_radius {δ : ℝ} (hδ : 0 < δ) :
    1 - Real.exp 1 / δ ≤ smallBallReal δ := by
  have h := finiteSmallBall_lower_large_radius hδ
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by positivity : 0 ≤ Real.exp 1 / δ)] at h
  exact (ENNReal.ofReal_le_iff_le_toReal (finiteSmallBall_ne_top δ)).mp h

theorem smallBallReal_tendsto_one : Tendsto smallBallReal atTop (nhds 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε heps
  filter_upwards [eventually_ge_atTop (max 1 (2 * Real.exp 1 / ε))] with δ hδ
  have hδ1 : 1 ≤ δ := (le_max_left _ _).trans hδ
  have hδpos : 0 < δ := by linarith
  have hb : 2 * Real.exp 1 / ε ≤ δ := (le_max_right _ _).trans hδ
  have hratio : Real.exp 1 / δ ≤ ε / 2 := by
    apply (div_le_iff₀ hδpos).mpr
    have h := (div_le_iff₀ heps).mp hb
    nlinarith
  have hlo := smallBallReal_lower_large_radius hδpos
  have hhi := smallBallReal_le_one δ
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Erdos524.FiniteSmallBallTail
