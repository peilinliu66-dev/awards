import Erdos524.GaussianSampleProduct
import Erdos524.GaussianDilationDensity
import Erdos524.GaussianDiagonalScaling
import Erdos524.FiniteKernelBox

/-! Quantitative finite Gaussian cube dilation from an energy-bounded sampled subvector. -/

namespace Erdos524.GaussianSampleDilation

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.GaussianSampleCovariance Erdos524.GaussianSampleProduct
open Erdos524.GaussianIndependentSumLaw Erdos524.GaussianDilationDensity
open Erdos524.GaussianBoxDensity Erdos524.GaussianDiagonalScaling Erdos524.FiniteKernelBox

variable {n m : ℕ}

theorem coordinate_dilation_lower {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hS : S.PosDef) {r Q : ℝ} (hr : 1 ≤ r)
    {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hQ : ∀ x ∈ A, x ⬝ᵥ S⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        coordinateGaussian S A ≤ coordinateGaussian S ((fun x ↦ r⁻¹ • x) ⁻¹' A) := by
  rw [coordinateGaussian_apply S hA,
    coordinateGaussian_apply S (hA.preimage (measurable_const_smul r⁻¹))]
  exact multivariate_gaussian_dilation_lower hS hr hA hQ

theorem product_dilation_lower {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hC : C.PosSemidef) (e : Fin (n + 1) → Fin (m + 1))
    (hA : (sampleCovariance C e).PosDef) (w : Fin (m + 1) → ℝ)
    {r Q : ℝ} (hr : 1 ≤ r)
    (hQ : ∀ x ∈ box (fun i ↦ w (e i)), x ⬝ᵥ (sampleCovariance C e)⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        coordinateGaussian C (box w) ≤
      ((coordinateGaussian (sampleCovariance C e)).prod (coordinateGaussian (residualCovariance C e)))
        {p | predictorWeights C e *ᵥ (r⁻¹ • p.1) + p.2 ∈ box w} := by
  let μ := coordinateGaussian (sampleCovariance C e)
  let ν := coordinateGaussian (residualCovariance C e)
  let H : Set ((Fin (n + 1) → ℝ) × (Fin (m + 1) → ℝ)) :=
    {p | predictorWeights C e *ᵥ p.1 + p.2 ∈ box w}
  let H' : Set ((Fin (n + 1) → ℝ) × (Fin (m + 1) → ℝ)) :=
    {p | predictorWeights C e *ᵥ (r⁻¹ • p.1) + p.2 ∈ box w}
  have hm : MeasurableSet H := (measurableSet_box w).preimage (by fun_prop)
  have hm' : MeasurableSet H' := (measurableSet_box w).preimage (by fun_prop)
  have he : coordinateGaussian C (box w) = (μ.prod ν) H := by
    rw [← regression_product_law hC e hA, Measure.map_apply (by fun_prop) (measurableSet_box w)]
    rfl
  rw [he]
  change _ ≤ (μ.prod ν) H'
  rw [Measure.prod_apply_symm hm, Measure.prod_apply_symm hm',
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [residual_samples_ae_zero hC e hA] with z hz
  let A := {x : Fin (n + 1) → ℝ | predictorWeights C e *ᵥ x + z ∈ box w}
  have hAm : MeasurableSet A := (measurableSet_box w).preimage (by fun_prop)
  have hAQ : ∀ x ∈ A, x ⬝ᵥ (sampleCovariance C e)⁻¹ *ᵥ x ≤ Q := by
    intro x hx
    apply hQ x
    intro i hi
    have hb := hx (e i) (Set.mem_univ _)
    simpa only [Pi.add_apply, predictor_action_at_sample C e hA, hz i, add_zero] using hb
  exact coordinate_dilation_lower hA hr hAm hAQ

theorem scaled_predictor_law {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hC : C.PosSemidef) (e : Fin (n + 1) → Fin (m + 1))
    (hA : (sampleCovariance C e).PosDef) (a : ℝ) :
    ((coordinateGaussian (sampleCovariance C e)).prod (coordinateGaussian (residualCovariance C e))).map
      (fun p ↦ predictorWeights C e *ᵥ (a • p.1) + p.2) =
      coordinateGaussian (a ^ 2 • predictorCovariance C e + residualCovariance C e) := by
  have h := predictor_plus_noise_law hA.posSemidef (residualCovariance_posSemidef hC e hA)
    (a • predictorWeights C e)
  have hmat : (a • predictorWeights C e) * sampleCovariance C e * (a • predictorWeights C e)ᵀ =
      a ^ 2 • predictorCovariance C e := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      predictor_covariance_identity C e hA]
    simp only [pow_two]
  rw [hmat] at h
  simpa only [Matrix.smul_mulVec, Matrix.mulVec_smul] using h

theorem coordinate_gaussian_scale_box {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hC : C.PosSemidef) {r : ℝ} (hr : 0 < r) (w : Fin (m + 1) → ℝ) :
    coordinateGaussian (r⁻¹ ^ 2 • C) (box w) =
      coordinateGaussian C (box (fun i ↦ r * w i)) := by
  have h := diagonal_gaussian_box hC (fun _ ↦ r⁻¹) (fun _ ↦ inv_pos.mpr hr)
    (fun i ↦ r * w i)
  have hm : diagonal (fun _ : Fin (m + 1) ↦ r⁻¹) * C * diagonal (fun _ ↦ r⁻¹) =
      r⁻¹ ^ 2 • C := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.smul_apply, smul_eq_mul]
    ring
  have hw : (fun i : Fin (m + 1) ↦ r⁻¹ * (r * w i)) = w := by
    ext i
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  rw [hm, hw] at h
  simpa only [coordinateGaussian_apply _ (measurableSet_box _)] using h

theorem finite_cube_dilation {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hC : C.PosSemidef) (e : Fin (n + 1) → Fin (m + 1))
    (hA : (sampleCovariance C e).PosDef) (w : Fin (m + 1) → ℝ)
    {r Q : ℝ} (hr : 1 ≤ r)
    (hQ : ∀ x ∈ box (fun i ↦ w (e i)), x ⬝ᵥ (sampleCovariance C e)⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        coordinateGaussian C (box w) ≤ coordinateGaussian C (box (fun i ↦ r * w i)) := by
  have hrpos : 0 < r := by linarith
  have hfirst := product_dilation_lower hC e hA w hr hQ
  have hlaw := congrArg (fun μ : Measure (Fin (m + 1) → ℝ) ↦ μ (box w))
    (scaled_predictor_law hC e hA r⁻¹)
  rw [Measure.map_apply (by fun_prop) (measurableSet_box w)] at hlaw
  change _ ≤ coordinateGaussian C (box (fun i ↦ r * w i))
  change _ = coordinateGaussian (r⁻¹ ^ 2 • predictorCovariance C e + residualCovariance C e) (box w) at hlaw
  have hlaw' : ((coordinateGaussian (sampleCovariance C e)).prod (coordinateGaussian (residualCovariance C e)))
      {p | predictorWeights C e *ᵥ (r⁻¹ • p.1) + p.2 ∈ box w} =
      coordinateGaussian (r⁻¹ ^ 2 • predictorCovariance C e + residualCovariance C e) (box w) := hlaw
  rw [hlaw'] at hfirst
  apply hfirst.trans
  have hS : (r⁻¹ ^ 2 • C).PosSemidef := hC.smul (sq_nonneg _)
  have hgap : (r⁻¹ ^ 2 • predictorCovariance C e + residualCovariance C e -
      r⁻¹ ^ 2 • C).PosSemidef := by
    have hi : r⁻¹ ≤ 1 := (inv_le_one₀ hrpos).mpr hr
    have hnonneg : 0 ≤ 1 - r⁻¹ ^ 2 := by nlinarith [inv_pos.mpr hrpos]
    have he : r⁻¹ ^ 2 • predictorCovariance C e + residualCovariance C e - r⁻¹ ^ 2 • C =
        (1 - r⁻¹ ^ 2) • residualCovariance C e := by
      unfold residualCovariance
      module
    rw [he]
    exact (residualCovariance_posSemidef hC e hA).smul hnonneg
  have hmono := gaussian_box_covariance_mono hS hgap w
  rw [← coordinateGaussian_apply _ (measurableSet_box _),
    ← coordinateGaussian_apply _ (measurableSet_box _), coordinate_gaussian_scale_box hC hrpos w] at hmono
  exact hmono

end Erdos524.GaussianSampleDilation
