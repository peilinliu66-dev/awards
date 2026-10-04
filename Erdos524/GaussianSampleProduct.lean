import Erdos524.GaussianSampleRegression
import Erdos524.GaussianIndependentSumLaw

/-! Independent sample/predictor-noise representation, with exact sample support. -/

namespace Erdos524.GaussianSampleProduct

open Set MeasureTheory ProbabilityTheory Matrix WithLp Filter
open Erdos524.GaussianSampleCovariance Erdos524.GaussianSampleRegression
open Erdos524.GaussianIndependentSumLaw

variable {n m : ℕ}

theorem regression_product_law {C : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ}
    (hC : C.PosSemidef) (e : Fin n → Fin (m + 1)) (hA : (sampleCovariance C e).PosDef) :
    ((coordinateGaussian (sampleCovariance C e)).prod (coordinateGaussian (residualCovariance C e))).map
      (fun p ↦ predictorWeights C e *ᵥ p.1 + p.2) = coordinateGaussian C := by
  have h := predictor_plus_noise_law hA.posSemidef (residualCovariance_posSemidef hC e hA)
    (predictorWeights C e)
  rw [predictor_covariance_identity C e hA] at h
  have he : predictorCovariance C e + residualCovariance C e = C := by
    unfold residualCovariance
    abel
  rwa [he] at h

theorem residual_samples_ae_zero {C : Matrix (Fin m) (Fin m) ℝ}
    (hC : C.PosSemidef) (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) :
    ∀ᵐ z ∂coordinateGaussian (residualCovariance C e), ∀ i, z (e i) = 0 := by
  have hmeas : MeasurableSet {z : Fin m → ℝ | ∀ i, z (e i) = 0} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i ↦ measurableSet_eq_fun (by fun_prop) measurable_const)
  change ∀ᵐ z ∂(multivariateGaussian 0 (residualCovariance C e)).map ofLp, ∀ i, z (e i) = 0
  rw [← remainder_law hC e hA]
  apply (ae_map_iff (remainder_measurable C e).aemeasurable hmeas).mpr
  exact Eventually.of_forall (fun z i ↦ remainder_at_sample C e hA z i)

end Erdos524.GaussianSampleProduct
