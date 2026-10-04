import Erdos524.GaussianProductDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Explicit Gaussian set/box probability bounds via invertible linear coordinates. -/

namespace Erdos524.GaussianBoxDensity

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Erdos524.GaussianProductDensity Erdos524.GaussianLevelSets

variable {n : ℕ}

noncomputable def normalization (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹) ^ (n + 1))

theorem pi_gaussian_apply_density (A : Set (Fin (n + 1) → ℝ)) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) A =
      normalization n * ∫⁻ x in A, ENNReal.ofReal (rho x) := by
  rw [pi_gaussian_eq_smul_radial, Measure.smul_apply, withDensity_apply']
  rfl

theorem pi_gaussian_le_volume (A : Set (Fin (n + 1) → ℝ)) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) A ≤ normalization n * volume A := by
  rw [pi_gaussian_apply_density]
  apply mul_le_mul_right
  calc
    (∫⁻ x in A, ENNReal.ofReal (rho x)) ≤ ∫⁻ _ in A, (1 : ℝ≥0∞) := by
      apply lintegral_mono
      intro x
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_one_iff.mpr (by have := energy_nonneg x; linarith)
    _ = volume A := setLIntegral_one A

theorem pi_gaussian_ge_volume (A : Set (Fin (n + 1) → ℝ)) (Q : ℝ)
    (hQ : ∀ x ∈ A, energy x ≤ Q) :
    normalization n * ENNReal.ofReal (Real.exp (-Q / 2)) * volume A ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) A := by
  rw [pi_gaussian_apply_density, mul_assoc]
  apply mul_le_mul_right
  rw [← setLIntegral_const A]
  apply setLIntegral_mono (ENNReal.measurable_ofReal.comp measurable_rho)
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have := hQ x hx
  linarith

noncomputable def inverseJacobian
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal |LinearMap.det (e.symm : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))|

theorem linearEquiv_gaussian_le_volume
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (A : Set (Fin (n + 1) → ℝ)) :
    (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) (e ⁻¹' A) ≤
      normalization n * inverseJacobian e * volume A := by
  have h := pi_gaussian_le_volume (e ⁻¹' A)
  rw [Measure.addHaar_preimage_continuousLinearEquiv volume e A] at h
  simpa only [inverseJacobian, mul_assoc] using h

theorem linearEquiv_gaussian_ge_volume
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (A : Set (Fin (n + 1) → ℝ)) (Q : ℝ)
    (hQ : ∀ y ∈ A, energy (e.symm y) ≤ Q) :
    normalization n * ENNReal.ofReal (Real.exp (-Q / 2)) * inverseJacobian e * volume A ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) (e ⁻¹' A) := by
  have h := pi_gaussian_ge_volume (e ⁻¹' A) Q (fun x hx ↦ by simpa using hQ (e x) hx)
  rw [Measure.addHaar_preimage_continuousLinearEquiv volume e A] at h
  simpa only [inverseJacobian, mul_assoc] using h

def box (w : Fin (n + 1) → ℝ) : Set (Fin (n + 1) → ℝ) :=
  Set.univ.pi (fun i ↦ Icc (-w i) (w i))

theorem measurableSet_box (w : Fin (n + 1) → ℝ) : MeasurableSet (box w) :=
  MeasurableSet.univ_pi (fun _ ↦ measurableSet_Icc)

theorem volume_box (w : Fin (n + 1) → ℝ) :
    volume (box w) = ∏ i, ENNReal.ofReal (2 * w i) := by
  rw [box, volume_pi_pi]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.volume_Icc]
  congr 1
  ring

theorem linearEquiv_gaussian_box_upper
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (w : Fin (n + 1) → ℝ) :
    ((Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map e) (box w) ≤
      normalization n * inverseJacobian e * ∏ i, ENNReal.ofReal (2 * w i) := by
  rw [Measure.map_apply e.continuous.measurable (measurableSet_box w), ← volume_box w]
  exact linearEquiv_gaussian_le_volume e (box w)

theorem linearEquiv_gaussian_box_lower
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ)) (w : Fin (n + 1) → ℝ) (Q : ℝ)
    (hQ : ∀ y ∈ box w, energy (e.symm y) ≤ Q) :
    normalization n * ENNReal.ofReal (Real.exp (-Q / 2)) * inverseJacobian e *
        (∏ i, ENNReal.ofReal (2 * w i)) ≤
      ((Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map e) (box w) := by
  rw [Measure.map_apply e.continuous.measurable (measurableSet_box w), ← volume_box w]
  exact linearEquiv_gaussian_ge_volume e (box w) Q hQ

end Erdos524.GaussianBoxDensity
