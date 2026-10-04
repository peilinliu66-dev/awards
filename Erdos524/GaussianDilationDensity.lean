import Erdos524.GaussianBoxDensity
import Erdos524.GaussianCovarianceCoordinates

/-! The finite Gaussian dilation likelihood-ratio lower bound on an energy-bounded set. -/

namespace Erdos524.GaussianDilationDensity

open Set MeasureTheory ProbabilityTheory Matrix
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
open scoped ENNReal BigOperators
open Erdos524.GaussianBoxDensity Erdos524.GaussianLevelSets

variable {n : ℕ}

theorem set_lintegral_rescale {r : ℝ} (hr : 0 < r)
    {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x in (fun x ↦ r⁻¹ • x) ⁻¹' A, f x) =
      ENNReal.ofReal (r ^ (n + 1)) * ∫⁻ x in A, f (r • x) := by
  let H := A.indicator (fun x ↦ f (r • x))
  have hH : Measurable H := (hf.comp (measurable_const_smul r)).indicator hA
  have h := lintegral_map (μ := (volume : Measure (Fin (n + 1) → ℝ))) hH (measurable_const_smul r⁻¹)
  rw [Measure.map_addHaar_smul (volume : Measure (Fin (n + 1) → ℝ)) (inv_ne_zero hr.ne'),
    lintegral_smul_measure] at h
  simp only [Module.finrank_pi, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (pow_nonneg hr.le _), smul_eq_mul] at h
  have he : (fun x ↦ H (r⁻¹ • x)) = ((fun x ↦ r⁻¹ • x) ⁻¹' A).indicator f := by
    funext x
    dsimp only [H]
    by_cases hx : r⁻¹ • x ∈ A
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x ↦ r⁻¹ • x) ⁻¹' A from hx)]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ (fun x ↦ r⁻¹ • x) ⁻¹' A from hx)]
  rw [he, lintegral_indicator (hA.preimage (measurable_const_smul r⁻¹))] at h
  change ENNReal.ofReal (r ^ (n + 1)) * ∫⁻ x, A.indicator (fun x ↦ f (r • x)) x = _ at h
  rw [lintegral_indicator hA] at h
  exact h.symm

theorem energy_smul (r : ℝ) (x : Fin (n + 1) → ℝ) : energy (r • x) = r ^ 2 * energy x := by
  simp only [energy, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem rho_dilation_lower {r Q : ℝ} (hr : 1 ≤ r) (x : Fin (n + 1) → ℝ)
    (hQ : energy x ≤ Q) :
    Real.exp (-((r ^ 2 - 1) * Q) / 2) * rho x ≤ rho (r • x) := by
  unfold rho
  rw [← Real.exp_add, energy_smul]
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (show 0 ≤ r ^ 2 - 1 by nlinarith) (sub_nonneg.mpr hQ)
  nlinarith

theorem pi_gaussian_dilation_lower {r Q : ℝ} (hr : 1 ≤ r)
    {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hQ : ∀ x ∈ A, energy x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) A ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) ((fun x ↦ r⁻¹ • x) ⁻¹' A) := by
  have hrpos : 0 < r := by linarith
  have hρ : Measurable (fun x : Fin (n + 1) → ℝ ↦ ENNReal.ofReal (rho x)) :=
    ENNReal.measurable_ofReal.comp measurable_rho
  let c := Real.exp (-((r ^ 2 - 1) * Q) / 2)
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hI : ENNReal.ofReal c * (∫⁻ x in A, ENNReal.ofReal (rho x)) ≤
      ∫⁻ x in A, ENNReal.ofReal (rho (r • x)) := by
    rw [← lintegral_const_mul (μ := volume.restrict A) (ENNReal.ofReal c)
      hρ]
    apply setLIntegral_mono (hρ.comp (measurable_const_smul r))
    intro x hx
    rw [← ENNReal.ofReal_mul hc]
    exact ENNReal.ofReal_le_ofReal (rho_dilation_lower hr x (hQ x hx))
  rw [pi_gaussian_apply_density, pi_gaussian_apply_density,
    set_lintegral_rescale hrpos hA (fun x ↦ ENNReal.ofReal (rho x)) hρ,
    ENNReal.ofReal_mul (pow_nonneg hrpos.le _)]
  change ENNReal.ofReal (r ^ (n + 1)) * ENNReal.ofReal c *
      (normalization n * ∫⁻ x in A, ENNReal.ofReal (rho x)) ≤
    normalization n * (ENNReal.ofReal (r ^ (n + 1)) * ∫⁻ x in A, ENNReal.ofReal (rho (r • x)))
  calc
    _ = (normalization n * ENNReal.ofReal (r ^ (n + 1))) *
        (ENNReal.ofReal c * ∫⁻ x in A, ENNReal.ofReal (rho x)) := by ring
    _ ≤ (normalization n * ENNReal.ofReal (r ^ (n + 1))) *
        (∫⁻ x in A, ENNReal.ofReal (rho (r • x))) := by gcongr
    _ = _ := by ring

theorem linearEquiv_gaussian_dilation_lower
    (e : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    {r Q : ℝ} (hr : 1 ≤ r) {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hQ : ∀ x ∈ A, energy (e.symm x) ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)) (e ⁻¹' A) ≤
      (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1))
        (e ⁻¹' ((fun x ↦ r⁻¹ • x) ⁻¹' A)) := by
  have h := pi_gaussian_dilation_lower hr (hA.preimage e.continuous.measurable)
    (fun x hx ↦ by simpa using hQ (e x) hx)
  have he : (fun x ↦ r⁻¹ • x) ⁻¹' (e ⁻¹' A) = e ⁻¹' ((fun x ↦ r⁻¹ • x) ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, map_smul]
  rwa [he] at h

theorem multivariate_gaussian_dilation_lower
    {S : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hS : S.PosDef)
    {r Q : ℝ} (hr : 1 ≤ r) {A : Set (Fin (n + 1) → ℝ)} (hA : MeasurableSet A)
    (hQ : ∀ x ∈ A, x ⬝ᵥ S⁻¹ *ᵥ x ≤ Q) :
    ENNReal.ofReal (r ^ (n + 1) * Real.exp (-((r ^ 2 - 1) * Q) / 2)) *
        (multivariateGaussian 0 S) (WithLp.ofLp ⁻¹' A) ≤
      (multivariateGaussian 0 S) (WithLp.ofLp ⁻¹' ((fun x ↦ r⁻¹ • x) ⁻¹' A)) := by
  let e := Erdos524.GaussianCovarianceCoordinates.sqrtEquiv S hS
  have h := linearEquiv_gaussian_dilation_lower e hr hA (fun x hx ↦ by
    rw [Erdos524.GaussianCovarianceCoordinates.energy_inverse_sqrt S hS]
    exact hQ x hx)
  have h0 := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ A)
    (Erdos524.GaussianCovarianceCoordinates.map_pi_sqrtEquiv S hS)
  rw [Measure.map_apply e.continuous.measurable hA, Measure.map_apply (by fun_prop) hA] at h0
  have hscaledA : MeasurableSet ((fun x : Fin (n + 1) → ℝ ↦ r⁻¹ • x) ⁻¹' A) :=
    hA.preimage (measurable_const_smul r⁻¹)
  have h1 := congrArg (fun μ : Measure (Fin (n + 1) → ℝ) ↦ μ ((fun x ↦ r⁻¹ • x) ⁻¹' A))
    (Erdos524.GaussianCovarianceCoordinates.map_pi_sqrtEquiv S hS)
  rw [Measure.map_apply e.continuous.measurable hscaledA,
    Measure.map_apply (by fun_prop) hscaledA] at h1
  rwa [h0, h1] at h

end Erdos524.GaussianDilationDensity
