import Erdos524.GaussianLinearLaw
import Erdos524.GaussianCovarianceComparison

/-! Finite Gaussian predictor plus independent Gaussian noise, in ordinary coordinate space. -/

namespace Erdos524.GaussianIndependentSumLaw

open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.GaussianLinearLaw Erdos524.GaussianCovarianceComparison

variable {n m : ℕ}

noncomputable def coordinateGaussian (S : Matrix (Fin n) (Fin n) ℝ) : Measure (Fin n → ℝ) :=
  (multivariateGaussian 0 S).map ofLp

instance coordinateGaussian_probability (S : Matrix (Fin n) (Fin n) ℝ) :
    IsProbabilityMeasure (coordinateGaussian S) := by
  unfold coordinateGaussian
  infer_instance

theorem coordinate_gaussian_add {S T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) :
    ((coordinateGaussian S).prod (coordinateGaussian T)).map (fun p ↦ p.1 + p.2) =
      coordinateGaussian (S + T) := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin (m + 1))) ↦ μ.map ofLp)
    (multivariate_gaussian_add hS hT)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  unfold coordinateGaussian
  rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact h

theorem coordinate_gaussian_linear {S : Matrix (Fin n) (Fin n) ℝ} (hS : S.PosSemidef)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (coordinateGaussian S).map (fun x ↦ A *ᵥ x) = coordinateGaussian (A * S * Aᵀ) := by
  unfold coordinateGaussian
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact gaussian_linear_map hS A

theorem predictor_plus_noise_law {S : Matrix (Fin n) (Fin n) ℝ}
    {T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hS : S.PosSemidef) (hT : T.PosSemidef) (W : Matrix (Fin (m + 1)) (Fin n) ℝ) :
    ((coordinateGaussian S).prod (coordinateGaussian T)).map (fun p ↦ W *ᵥ p.1 + p.2) =
      coordinateGaussian (W * S * Wᵀ + T) := by
  have hD : (W * S * Wᵀ).PosSemidef := by
    have h := hS.mul_mul_conjTranspose_same W
    have he : Wᴴ = Wᵀ := by ext i j; simp
    rwa [he] at h
  have hprod : ((coordinateGaussian S).prod (coordinateGaussian T)).map
      (Prod.map (fun x ↦ W *ᵥ x) id) =
      ((coordinateGaussian S).map (fun x ↦ W *ᵥ x)).prod (coordinateGaussian T) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (coordinateGaussian S) (coordinateGaussian T) (by fun_prop) measurable_id).symm
  calc
    _ = (((coordinateGaussian S).prod (coordinateGaussian T)).map
        (Prod.map (fun x ↦ W *ᵥ x) id)).map (fun p ↦ p.1 + p.2) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ((coordinateGaussian (W * S * Wᵀ)).prod (coordinateGaussian T)).map (fun p ↦ p.1 + p.2) := by
      rw [hprod, coordinate_gaussian_linear hS W]
    _ = _ := coordinate_gaussian_add hD hT

theorem coordinateGaussian_apply (S : Matrix (Fin n) (Fin n) ℝ)
    {A : Set (Fin n → ℝ)} (hA : MeasurableSet A) :
    coordinateGaussian S A = (multivariateGaussian 0 S) (ofLp ⁻¹' A) :=
  Measure.map_apply (by fun_prop) hA

end Erdos524.GaussianIndependentSumLaw
