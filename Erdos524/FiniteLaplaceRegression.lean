import Erdos524.AffineGaussianBand

/-! Regression on the zero-parameter coordinate of an actual finite Laplace Gaussian. -/

namespace Erdos524.FiniteLaplaceRegression

open Set MeasureTheory ProbabilityTheory Matrix WithLp
open scoped BigOperators ProbabilityTheory
open Erdos524.LaplaceKernelComparison Erdos524.IntegralGramComparison
open Erdos524.FiniteGaussianRegression Erdos524.FiniteGaussianTailBound
open Erdos524.GaussianCoordinateProjection

variable {n : ℕ}

noncomputable def zeroCoefficient (u : ℝ) : ℝ := ∫ s, laplace u s ∂intervalMeasure

noncomputable def jointMeasure (u : Fin (n + 1) → ℝ) : Measure (EuclideanSpace ℝ (Fin (n + 2))) :=
  multivariateGaussian 0 (finiteKernel (Fin.cons 0 u))

instance joint_probability (u : Fin (n + 1) → ℝ) : IsProbabilityMeasure (jointMeasure u) := by
  unfold jointMeasure
  infer_instance

def base (z : EuclideanSpace ℝ (Fin (n + 2))) : ℝ := z 0
def sample (z : EuclideanSpace ℝ (Fin (n + 2))) : Fin 1 → ℝ := fun _ ↦ z 0
def evaluation (z : EuclideanSpace ℝ (Fin (n + 2))) : Fin (n + 1) → ℝ := fun i ↦ z i.succ
noncomputable def weights (u : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin 1) ℝ :=
  fun i _ ↦ zeroCoefficient (u i)
noncomputable def laplaceResidual (u : Fin (n + 1) → ℝ) :=
  residual (weights u) (sample (n := n)) evaluation

theorem cons_nonneg (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) : ∀ i : Fin (n + 2), 0 ≤ (Fin.cons 0 u : Fin (n + 2) → ℝ) i := by
  intro i
  refine Fin.cases (by simp) (fun j ↦ ?_) i
  simpa only [Fin.cons_succ] using hu j

theorem base_covariance (u : Fin (n + 1) → ℝ) : finiteKernel (Fin.cons 0 u) 0 0 = 1 := by
  simp [finiteKernel_apply]

theorem base_eval_covariance (u : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    finiteKernel (Fin.cons 0 u) 0 i.succ = zeroCoefficient (u i) := by
  unfold finiteKernel integralGram zeroCoefficient
  simp only [Fin.cons_zero, Fin.cons_succ, laplace, neg_zero, zero_mul, Real.exp_zero, one_mul]

theorem zeroCoefficient_lower {u T : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    Real.exp (-T) ≤ zeroCoefficient u := by
  have hm := (memLp_laplace_interval hu).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h := integral_mono_ae (integrable_const (Real.exp (-T))) hm (by
    change ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), Real.exp (-T) ≤ laplace u s
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    unfold laplace
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hs.2 hu
    nlinarith)
  simpa [integral_const, intervalMeasure, Measure.real, Real.volume_Icc, zeroCoefficient] using h

theorem joint_gaussian (u : Fin (n + 1) → ℝ) :
    HasGaussianLaw (fun z ↦ (sample z, evaluation z)) (jointMeasure u) := by
  have h : HasGaussianLaw id (jointMeasure u) := by unfold jointMeasure; exact IsGaussian.hasGaussianLaw_id
  let A : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] (Fin 1 → ℝ) :=
    ContinuousLinearMap.pi (fun _ ↦ EuclideanSpace.proj 0)
  let B : EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] (Fin (n + 1) → ℝ) :=
    ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj i.succ)
  exact h.map_fun (A.prod B)

theorem normal_equations (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) (i : Fin 1) (j : Fin (n + 1)) :
    cov[fun z ↦ sample z i, fun z ↦ evaluation z j; jointMeasure u] =
      ∑ k, weights u j k * cov[fun z ↦ sample z i, fun z ↦ sample z k; jointMeasure u] := by
  have hS := finiteKernel_posSemidef (Fin.cons 0 u) (cons_nonneg u hu)
  simp only [sample, evaluation, jointMeasure, weights, covariance_eval_multivariateGaussian hS,
    base_covariance, base_eval_covariance, mul_one]
  simp

theorem base_residual_independent (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) :
    IndepFun (base (n := n)) (laplaceResidual u) (jointMeasure u) := by
  have h := residual_independent (weights u) (joint_gaussian u) (normal_equations u hu)
  exact h.comp (measurable_pi_apply 0) measurable_id

theorem residual_gaussian (u : Fin (n + 1) → ℝ) : HasGaussianLaw (laplaceResidual u) (jointMeasure u) :=
  (joint_residual_gaussian (weights u) (joint_gaussian u)).snd

theorem base_law (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (jointMeasure u).map base = gaussianReal 0 1 := by
  have h := (joint_gaussian u).fst.eval 0
  change HasGaussianLaw (base (n := n)) (jointMeasure u) at h
  rw [h.map_eq_gaussianReal]
  have hS := finiteKernel_posSemidef (Fin.cons 0 u) (cons_nonneg u hu)
  change gaussianReal (∫ z, z 0 ∂multivariateGaussian 0 (finiteKernel (Fin.cons 0 u)))
    (variance (fun z ↦ z 0) (multivariateGaussian 0 (finiteKernel (Fin.cons 0 u)))).toNNReal = _
  rw [gaussian_coordinate_mean, variance_eval_multivariateGaussian hS, base_covariance]
  simp

theorem evaluation_law (u : Fin (n + 1) → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (jointMeasure u).map evaluation = (multivariateGaussian 0 (finiteKernel u)).map ofLp := by
  have h := gaussian_coordinate_projection
    (finiteKernel_posSemidef (Fin.cons 0 u) (cons_nonneg u hu)) Fin.succ
  have he : (finiteKernel (Fin.cons 0 u)).submatrix Fin.succ Fin.succ = finiteKernel u := by
    ext i j
    rfl
  rw [he] at h
  exact h

theorem reconstruction (u : Fin (n + 1) → ℝ) (z : EuclideanSpace ℝ (Fin (n + 2)))
    (i : Fin (n + 1)) :
    evaluation z i = zeroCoefficient (u i) * base z + laplaceResidual u z i := by
  unfold laplaceResidual Erdos524.FiniteGaussianRegression.residual weights sample evaluation base
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_one]
  ring

theorem zeroCoefficient_upper {u : ℝ} (hu : 0 ≤ u) : zeroCoefficient u ≤ 1 := by
  have hm := (memLp_laplace_interval hu).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have h := integral_mono_ae hm (integrable_const (1 : ℝ)) (by
    change ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), laplace u s ≤ 1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    unfold laplace
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hs.1))
  simpa [integral_const, intervalMeasure, Measure.real, Real.volume_Icc, zeroCoefficient] using h

theorem zeroCoefficient_zero : zeroCoefficient 0 = 1 := by
  simp [zeroCoefficient, laplace, intervalMeasure, Measure.real, Real.volume_Icc]

noncomputable def residualMap (u : Fin (n + 1) → ℝ) :
    EuclideanSpace ℝ (Fin (n + 2)) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ EuclideanSpace.proj i.succ -
    zeroCoefficient (u i) • EuclideanSpace.proj 0)

theorem residualMap_apply (u : Fin (n + 1) → ℝ) (z : EuclideanSpace ℝ (Fin (n + 2))) :
    residualMap u z = laplaceResidual u z := by
  funext i
  change z i.succ - zeroCoefficient (u i) * z 0 = laplaceResidual u z i
  have h := reconstruction u z i
  change z i.succ = zeroCoefficient (u i) * z 0 + laplaceResidual u z i at h
  linarith

end Erdos524.FiniteLaplaceRegression
