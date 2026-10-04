import Erdos524.TwoSidedLaplaceKernels

namespace Erdos524.TwoSidedGaussianLimit
open MeasureTheory ProbabilityTheory Matrix WithLp Set
open scoped ProbabilityTheory
open Erdos524.TwoColorKernel Erdos524.TwoSidedLaplaceKernels
open Erdos524.LaplaceKernelComparison Erdos524.IntegralGramComparison
open Erdos524.GaussianCoordinateProjection Erdos524.GramGaussianCoupling
open Erdos524.FiniteCouplingComparison

noncomputable def exactFamily {d : ℕ} (u : Fin d → ℝ) : Fin (d+d) → Fin 2 × ℝ → ℝ :=
  Fin.addCases (fun j => exactPair 1 (u j)) (fun j => exactPair (-1) (u j))

theorem exactFamily_memLp {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) :
    ∀ j, MemLp (exactFamily u j) 2 colorMeasure := by
  intro j
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · simpa only [exactFamily,Fin.addCases_left] using memLp_exactPair 1 (hu k)
  · simpa only [exactFamily,Fin.addCases_right] using memLp_exactPair (-1) (hu k)

theorem exactGram_left {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) :
    (integralGram (exactFamily u) colorMeasure).submatrix (Fin.castAdd d) (Fin.castAdd d)=finiteKernel u := by
  ext i j
  simp only [Matrix.submatrix_apply,integralGram,exactFamily,Fin.addCases_left]
  rw [exactPair_covariance 1 1 (hu i) (hu j)]
  norm_num
  rfl

theorem exactGram_right {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) :
    (integralGram (exactFamily u) colorMeasure).submatrix (Fin.natAdd d) (Fin.natAdd d)=finiteKernel u := by
  ext i j
  simp only [Matrix.submatrix_apply,integralGram,exactFamily,Fin.addCases_right]
  rw [exactPair_covariance (-1) (-1) (hu i) (hu j)]
  norm_num
  rfl

theorem exactGram_cross {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) (i j : Fin d) :
    integralGram (exactFamily u) colorMeasure (Fin.castAdd d i) (Fin.natAdd d j)=0 := by
  simp only [integralGram,exactFamily,Fin.addCases_left,Fin.addCases_right]
  rw [exactPair_covariance 1 (-1) (hu i) (hu j)]
  norm_num

theorem exactPair_independent {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) :
    IndepFun (fun z : EuclideanSpace ℝ (Fin (d+d)) => fun j : Fin d => z (Fin.castAdd d j))
      (fun z => fun j : Fin d => z (Fin.natAdd d j)) (multivariateGaussian 0 (integralGram (exactFamily u) colorMeasure)) := by
  have hid : HasGaussianLaw id (multivariateGaussian (0 : EuclideanSpace ℝ (Fin (d+d))) (integralGram (exactFamily u) colorMeasure)) := IsGaussian.hasGaussianLaw_id
  let L : EuclideanSpace ℝ (Fin (d+d)) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun j => EuclideanSpace.proj (Fin.castAdd d j))
  let R : EuclideanSpace ℝ (Fin (d+d)) →L[ℝ] (Fin d → ℝ) := ContinuousLinearMap.pi (fun j => EuclideanSpace.proj (Fin.natAdd d j))
  have h := hid.map_fun (L.prod R)
  apply h.indepFun_of_covariance_eval
  intro i j
  change cov[fun z : EuclideanSpace ℝ (Fin (d+d)) => z (Fin.castAdd d i), fun z => z (Fin.natAdd d j);
    multivariateGaussian 0 (integralGram (exactFamily u) colorMeasure)]=0
  rw [covariance_eval_multivariateGaussian (integralGram_posSemidef _ _ (exactFamily_memLp u hu))]
  exact exactGram_cross u hu i j

theorem exactFamily_box_square {d : ℕ} (u : Fin d → ℝ) (hu : ∀ j, 0≤u j) (r : ℝ) :
    gramBoxProbability (exactFamily u) colorMeasure r=(gramBoxProbability (fun j => laplace (u j)) intervalMeasure r)^2 := by
  let P := multivariateGaussian 0 (integralGram (exactFamily u) colorMeasure)
  let X : EuclideanSpace ℝ (Fin (d+d)) → Fin d → ℝ := fun z j => z (Fin.castAdd d j)
  let Y : EuclideanSpace ℝ (Fin (d+d)) → Fin d → ℝ := fun z j => z (Fin.natAdd d j)
  let B : Set (Fin d → ℝ) := box id r
  have hB : MeasurableSet B := box_measurable id (by intro j; fun_prop) r
  have hS := integralGram_posSemidef _ _ (exactFamily_memLp u hu)
  have hXL := gaussian_coordinate_projection hS (Fin.castAdd d)
  have hYL := gaussian_coordinate_projection hS (Fin.natAdd d)
  rw [exactGram_left u hu] at hXL
  rw [exactGram_right u hu] at hYL
  have hXm := congrArg (fun ν : Measure (Fin d → ℝ) => ν B) hXL
  have hYm := congrArg (fun ν : Measure (Fin d → ℝ) => ν B) hYL
  rw [Measure.map_apply (by fun_prop) hB,Measure.map_apply (by fun_prop) hB] at hXm hYm
  have hind := (exactPair_independent u hu).measure_inter_preimage_eq_mul B B hB hB
  have he : {z : EuclideanSpace ℝ (Fin (d+d)) | ∀ j, |z j|≤r}=X ⁻¹' B ∩ Y ⁻¹' B := by
    ext z
    constructor
    · intro hz
      exact ⟨fun j => hz (Fin.castAdd d j),fun j => hz (Fin.natAdd d j)⟩
    · intro hz j
      exact Fin.addCases (fun k => hz.1 k) (fun k => hz.2 k) j
  unfold gramBoxProbability Measure.real
  rw [he]
  change (P (X ⁻¹' B ∩ Y ⁻¹' B)).toReal=_
  rw [hind,hXm,hYm,ENNReal.toReal_mul]
  simp only [finiteKernel,B,box,Set.preimage_setOf_eq,id_eq,pow_two]

end Erdos524.TwoSidedGaussianLimit
