import Erdos524.FiniteGaussianRegression
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Equality in law for finite Gaussian vectors from coordinate means/covariances. -/

namespace Erdos524.GaussianVectorLaw

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ProbabilityTheory

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} {Q : Measure Ω'} {n : ℕ}
variable {X : Ω → (Fin n → ℝ)} {Y : Ω' → (Fin n → ℝ)}

theorem map_eq_of_mean_covariance (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y Q)
    (hmX : Measurable X) (hmY : Measurable Y)
    (hmean : ∀ i, (∫ ω, X ω i ∂P) = ∫ ω, Y ω i ∂Q)
    (hcov : ∀ i j, cov[fun ω ↦ X ω i, fun ω ↦ X ω j; P] =
      cov[fun ω ↦ Y ω i, fun ω ↦ Y ω j; Q]) : P.map X = Q.map Y := by
  haveI := hX.isProbabilityMeasure
  haveI := hY.isProbabilityMeasure
  have hXE := hX.toLp_pi 2
  have hYE := hY.toLp_pi 2
  haveI := hXE.isGaussian_map
  haveI := hYE.isGaussian_map
  have he : P.map (fun ω ↦ toLp 2 (X ω)) = Q.map (fun ω ↦ toLp 2 (Y ω)) := by
    apply IsGaussian.ext
    · rw [integral_map hXE.aemeasurable (by fun_prop),
        integral_map hYE.aemeasurable (by fun_prop)]
      ext i
      have hx := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hXE.integrable
      have hy := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm hYE.integrable
      simp only [EuclideanSpace.coe_proj, id_eq] at hx hy ⊢
      exact hx.symm.trans ((hmean i).trans hy)
    · rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        fun i j ↦ ?_
      simp only [ContinuousLinearMap.toBilinForm_apply]
      change covarianceBilin (P.map (fun ω ↦ toLp 2 (fun i ↦ X ω i)))
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) =
        covarianceBilin (Q.map (fun ω ↦ toLp 2 (fun i ↦ Y ω i)))
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)
      rw [covarianceBilin_apply_basisFun (fun k ↦ (hX.eval k).memLp_two),
        covarianceBilin_apply_basisFun (fun k ↦ (hY.eval k).memLp_two)]
      exact hcov i j
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦ μ.map ofLp) he
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end Erdos524.GaussianVectorLaw
