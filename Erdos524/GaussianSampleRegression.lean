import Erdos524.GaussianSampleCovariance
import Erdos524.FiniteGaussianRegression
import Erdos524.GaussianCoordinateProjection

/-! Actual finite Gaussian sample regression for an arbitrary positive-definite sampled covariance. -/

namespace Erdos524.GaussianSampleRegression

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ProbabilityTheory
open Erdos524.GaussianSampleCovariance Erdos524.FiniteGaussianRegression
open Erdos524.FiniteGaussianTailBound Erdos524.GaussianVectorLaw Erdos524.GaussianCoordinateProjection

variable {n m : ℕ}

def samples (e : Fin n → Fin m) (z : EuclideanSpace ℝ (Fin m)) : Fin n → ℝ := fun i ↦ z (e i)
noncomputable def remainder (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :=
  residual (predictorWeights C e) (samples e) ofLp

theorem joint_gaussian (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :
    HasGaussianLaw (fun z ↦ (samples e z, ofLp z)) (multivariateGaussian 0 C) := by
  have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) C) := IsGaussian.hasGaussianLaw_id
  let A : EuclideanSpace ℝ (Fin m) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj (e i))
  let B := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  exact h.map_fun (A.prod B)

theorem actual_normal_equations {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) (i : Fin n) (j : Fin m) :
    cov[fun z ↦ samples e z i, fun z ↦ ofLp z j; multivariateGaussian 0 C] =
      ∑ k, predictorWeights C e j k *
        cov[fun z ↦ samples e z i, fun z ↦ samples e z k; multivariateGaussian 0 C] := by
  simp only [samples, covariance_eval_multivariateGaussian hC]
  exact predictor_normal_equations hC e hA i j

theorem samples_remainder_independent {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) :
    IndepFun (samples e) (remainder C e) (multivariateGaussian 0 C) :=
  residual_independent (predictorWeights C e) (joint_gaussian C e) (actual_normal_equations hC e hA)

theorem remainder_gaussian (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :
    HasGaussianLaw (remainder C e) (multivariateGaussian 0 C) :=
  (joint_residual_gaussian (predictorWeights C e) (joint_gaussian C e)).snd

theorem remainder_measurable (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) :
    Measurable (remainder C e) := by
  unfold remainder Erdos524.FiniteGaussianRegression.residual samples
  fun_prop

theorem remainder_covariance {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) (j l : Fin m) :
    cov[fun z ↦ remainder C e z j, fun z ↦ remainder C e z l; multivariateGaussian 0 C] =
      residualCovariance C e j l := by
  have h := covariance_residual (predictorWeights C e) (joint_gaussian C e)
    (actual_normal_equations hC e hA) j l
  simp only [samples, covariance_eval_multivariateGaussian hC] at h
  change cov[fun z ↦ remainder C e z j, fun z ↦ remainder C e z l; multivariateGaussian 0 C] = _ at h
  rw [h]
  change C j l - (∑ k, predictorWeights C e j k * C (e k) l) =
    C j l - (∑ k, predictorWeights C e j k * C l (e k))
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hs : C (e k) l = C l (e k) :=
    congrArg (fun M : Matrix (Fin m) (Fin m) ℝ ↦ M l (e k)) hC.isHermitian.isSymm
  rw [hs]

theorem remainder_mean (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m) (j : Fin m) :
    (∫ z, remainder C e z j ∂multivariateGaussian 0 C) = 0 := by
  have hX (k : Fin n) := ((joint_gaussian C e).fst.eval k).integrable
  have hY := ((joint_gaussian C e).snd.eval j).integrable
  have hW (k : Fin n) : Integrable (fun z ↦ predictorWeights C e j k * samples e z k)
      (multivariateGaussian 0 C) := (hX k).const_mul _
  change (∫ z, ofLp z j - ∑ k, predictorWeights C e j k * samples e z k ∂multivariateGaussian 0 C) = 0
  rw [integral_sub hY (integrable_finset_sum Finset.univ (fun k _ ↦ hW k)),
    integral_finsetSum Finset.univ (fun k _ ↦ hW k)]
  simp only [samples, integral_const_mul, gaussian_coordinate_mean, mul_zero, Finset.sum_const_zero, sub_self]

theorem sample_law {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef) (e : Fin n → Fin m) :
    (multivariateGaussian 0 C).map (samples e) =
      (multivariateGaussian 0 (sampleCovariance C e)).map ofLp := gaussian_coordinate_projection hC e

theorem remainder_law {C : Matrix (Fin m) (Fin m) ℝ} (hC : C.PosSemidef)
    (e : Fin n → Fin m) (hA : (sampleCovariance C e).PosDef) :
    (multivariateGaussian 0 C).map (remainder C e) =
      (multivariateGaussian 0 (residualCovariance C e)).map ofLp := by
  have hR := residualCovariance_posSemidef hC e hA
  have hY : HasGaussianLaw (ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ))
      (multivariateGaussian 0 (residualCovariance C e)) := by
    have h : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) (residualCovariance C e)) :=
      IsGaussian.hasGaussianLaw_id
    exact h.map_fun (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ ℝ)).toContinuousLinearMap
  apply map_eq_of_mean_covariance (remainder_gaussian C e) hY (remainder_measurable C e) (by fun_prop)
  · intro j
    rw [remainder_mean, gaussian_coordinate_mean]
  · intro j l
    rw [remainder_covariance hC e hA, covariance_eval_multivariateGaussian hR]

theorem remainder_at_sample (C : Matrix (Fin m) (Fin m) ℝ) (e : Fin n → Fin m)
    (hA : (sampleCovariance C e).PosDef) (z : EuclideanSpace ℝ (Fin m)) (i : Fin n) :
    remainder C e z (e i) = 0 := by
  change z (e i) - ∑ k, predictorWeights C e (e i) k * z (e k) = 0
  simp_rw [predictor_at_sample C e hA i]
  change z (e i) - ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ samples e z) i = 0
  simp [samples]

end Erdos524.GaussianSampleRegression
