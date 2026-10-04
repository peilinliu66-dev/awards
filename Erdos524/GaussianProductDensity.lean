import Erdos524.GaussianLevelSets
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! Standard Gaussian product measure and its radial density. -/

namespace Erdos524.GaussianProductDensity

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Erdos524.GaussianLevelSets

variable {n : ℕ}

noncomputable def pdfProduct (x : Fin (n + 1) → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 1 (x i)

theorem pdfProduct_nonneg (x : Fin (n + 1) → ℝ) : 0 ≤ pdfProduct x := by
  exact Finset.prod_nonneg fun i _ ↦ gaussianPDFReal_nonneg 0 1 (x i)

theorem integrable_pdfProduct : Integrable (pdfProduct (n := n)) volume :=
  Integrable.fintype_prod (fun _ ↦ integrable_gaussianPDFReal 0 1)

theorem pi_gaussian_eq_withDensity :
    Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (pdfProduct x)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_pdfProduct.restrict)
      (Filter.Eventually.of_forall pdfProduct_nonneg)]
  change ENNReal.ofReal
    (∫ x, pdfProduct x ∂((Measure.pi fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)).restrict
      (Set.univ.pi s))) = _
  rw [Measure.restrict_pi_pi]
  simp only [pdfProduct, integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
    integral_nonneg (fun x ↦ gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i hi
  exact (gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0) (s i)).symm

theorem pdfProduct_eq_rho (x : Fin (n + 1) → ℝ) :
    pdfProduct x = ((Real.sqrt (2 * Real.pi))⁻¹) ^ (n + 1) * rho x := by
  simp only [pdfProduct, gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 1
  unfold rho energy
  congr 1
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem pi_gaussian_eq_smul_radial :
    Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) =
      ENNReal.ofReal (((Real.sqrt (2 * Real.pi))⁻¹) ^ (n + 1)) •
        volume.withDensity (fun x : Fin (n + 1) → ℝ ↦ ENNReal.ofReal (rho x)) := by
  rw [pi_gaussian_eq_withDensity]
  have hc : 0 ≤ ((Real.sqrt (2 * Real.pi))⁻¹) ^ (n + 1) := by positivity
  simp_rw [pdfProduct_eq_rho, ENNReal.ofReal_mul hc]
  exact withDensity_smul _ (ENNReal.measurable_ofReal.comp measurable_rho)

end Erdos524.GaussianProductDensity
