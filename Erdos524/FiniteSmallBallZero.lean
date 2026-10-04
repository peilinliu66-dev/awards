import Erdos524.FiniteSmallBallContinuity

/-! The zero endpoint and global continuity of the finite small-ball distribution. -/

namespace Erdos524.FiniteSmallBallZero

open Set Filter MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal
open Erdos524.FiniteSmallBallEnvelope Erdos524.FiniteSmallBallBasic
open Erdos524.FiniteSmallBallContinuity Erdos524.LaplaceKernelComparison
open Erdos524.GaussianBoxDensity Erdos524.AffineGaussianBand

theorem finiteSmallBall_le_standard_interval (δ : ℝ) :
    finiteSmallBall δ ≤ (gaussianReal 0 1) (Icc (-δ) δ) := by
  have h := finiteSmallBall_le_evaluation δ 0 (fun _ ↦ 0)
  have he : finiteKernel (fun _ : Fin 1 ↦ (0 : ℝ)) = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    fin_cases i
    fin_cases j
    norm_num [finiteKernel_apply, Matrix.one_apply]
  change finiteSmallBall δ ≤ (multivariateGaussian 0 (finiteKernel (fun _ : Fin 1 ↦ (0 : ℝ))))
    (ofLp ⁻¹' box (fun _ ↦ δ)) at h
  rw [he] at h
  have hs : (ofLp : EuclideanSpace ℝ (Fin 1) → (Fin 1 → ℝ)) ⁻¹' box (fun _ ↦ δ) =
      (fun z ↦ z 0) ⁻¹' Icc (-δ) δ := by
    ext z
    constructor
    · intro hz
      exact hz 0 (Set.mem_univ 0)
    · intro hz i hi
      have heq : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      exact hz
  rw [hs] at h
  have hmp := (measurePreserving_eval_multivariateGaussian
    (μ := (0 : EuclideanSpace ℝ (Fin 1)))
    (S := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosDef.one.posSemidef (i := 0)).measure_preimage (s := Icc (-δ) δ)
    measurableSet_Icc.nullMeasurableSet
  have hmp' : (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))
      ((fun z ↦ z 0) ⁻¹' Icc (-δ) δ) = (gaussianReal 0 1) (Icc (-δ) δ) := by simpa using hmp
  exact h.trans_eq hmp'

theorem finiteSmallBall_linear_upper (δ : ℝ) : finiteSmallBall δ ≤ ENNReal.ofReal (2 * δ) := by
  have h := (finiteSmallBall_le_standard_interval δ).trans (standardGaussian_le_volume (Icc (-δ) δ))
  rw [Real.volume_Icc] at h
  convert h using 1 <;> congr 1 <;> ring

theorem smallBallReal_linear_upper {δ : ℝ} (hδ : 0 ≤ δ) : smallBallReal δ ≤ 2 * δ := by
  have h := (ENNReal.toReal_le_toReal (finiteSmallBall_ne_top _) (by finiteness)).mpr
    (finiteSmallBall_linear_upper δ)
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ)] at h
  exact h

theorem smallBallReal_nonpos {δ : ℝ} (hδ : δ ≤ 0) : smallBallReal δ = 0 := by
  simp only [smallBallReal, finiteSmallBall_nonpos hδ, ENNReal.toReal_zero]

theorem smallBallReal_continuousAt_nonpos {δ : ℝ} (hδ : δ ≤ 0) : ContinuousAt smallBallReal δ := by
  apply Metric.continuousAt_iff.mpr
  intro ε heps
  refine ⟨ε / 4, by linarith, ?_⟩
  intro x hx
  have hdist : |x - δ| < ε / 4 := by simpa only [Real.dist_eq] using hx
  have hxnonneg : 0 ≤ smallBallReal x := ENNReal.toReal_nonneg
  rw [smallBallReal_nonpos hδ, Real.dist_eq, sub_zero, abs_of_nonneg hxnonneg]
  by_cases hx0 : x ≤ 0
  · rw [smallBallReal_nonpos hx0]
    exact heps
  · have hxpos : 0 < x := lt_of_not_ge hx0
    have hupper := smallBallReal_linear_upper hxpos.le
    have hnear := (abs_lt.mp hdist).2
    linarith

theorem smallBallReal_continuous : Continuous smallBallReal := by
  apply continuous_iff_continuousAt.mpr
  intro δ
  by_cases hδ : δ ≤ 0
  · exact smallBallReal_continuousAt_nonpos hδ
  · exact smallBallReal_continuousAt_pos (lt_of_not_ge hδ)

theorem standardGaussian_interval_pos {a b : ℝ} (hab : a < b) :
    0 < (gaussianReal 0 1) (Icc a b) := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hvol := gaussianReal_absolutelyContinuous' 0 (by norm_num : (1 : NNReal) ≠ 0) hzero
  rw [Real.volume_Icc] at hvol
  exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) hvol

end Erdos524.FiniteSmallBallZero
