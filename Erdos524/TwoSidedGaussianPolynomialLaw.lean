import Erdos524.ParityPowerSum
import Erdos524.GaussianPolynomialLaw

namespace Erdos524.TwoSidedGaussianPolynomialLaw
open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.TwoSidedLaplaceKernels Erdos524.TwoColorKernel Erdos524.TwoSidedStepGram
open Erdos524.ParityPowerSum Erdos524.IntegralGramComparison Erdos524.GaussianPolynomialLaw

noncomputable def phaseMatrix {M d : ℕ} (σ u : Fin d → ℝ) : Matrix (Fin d) (Fin (2*M)) ℝ :=
  fun j i => (σ j)^(i.val+1)*Real.exp (-u j*((i.val+1:ℕ):ℝ)/(2*(M:ℝ)))/Real.sqrt (2*(M:ℝ))

theorem phaseMatrix_gram {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) :
    phaseMatrix (M := M) σ u*(phaseMatrix σ u)ᵀ=integralGram (fun j => stepPair M (σ j) (u j)) colorMeasure := by
  have hMp : (0:ℝ)<M := by exact_mod_cast hM
  have hs : Real.sqrt (2*(M:ℝ))^2=2*(M:ℝ) := Real.sq_sqrt (by positivity)
  ext i j
  change (∑ k, phaseMatrix σ u i k*phaseMatrix σ u j k)=_
  unfold phaseMatrix
  simp_rw [div_mul_div_comm,← pow_two,hs]
  rw [← Finset.sum_div]
  have he : (∑ k : Fin (2*M), (σ i)^(k.val+1)*Real.exp (-u i*((k.val+1:ℕ):ℝ)/(2*(M:ℝ)))*
      ((σ j)^(k.val+1)*Real.exp (-u j*((k.val+1:ℕ):ℝ)/(2*(M:ℝ)))))=
      ∑ k : Fin (2*M), (σ i)^(k.val+1)*(σ j)^(k.val+1)*Real.exp (-u i*((k.val+1:ℕ):ℝ)/(2*(M:ℝ)))*Real.exp (-u j*((k.val+1:ℕ):ℝ)/(2*(M:ℝ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [he,parity_exponential_sum hM (hσ i) (hσ j)]
  exact (stepPair_covariance hM (σ i) (σ j) (hu i) (hu j)).symm

theorem gaussian_phase_polynomial_law {M d : ℕ} (hM : 0<M) (σ u : Fin d → ℝ)
    (hσ : ∀ j, (σ j)^2=1) (hu : ∀ j, 0≤u j) :
    (Measure.pi (fun _ : Fin (2*M) => gaussianReal 0 1)).map (fun z => phaseMatrix σ u*ᵥz)=
      (multivariateGaussian 0 (integralGram (fun j => stepPair M (σ j) (u j)) colorMeasure)).map ofLp := by
  have h := gaussian_pi_linear_map (phaseMatrix (M := M) σ u)
  rwa [phaseMatrix_gram hM σ u hσ hu] at h

end Erdos524.TwoSidedGaussianPolynomialLaw
