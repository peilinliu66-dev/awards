import Erdos524.DiscreteLaplaceGram
import Erdos524.GaussianLinearLaw
import Erdos524.PolynomialLaplaceGrid

namespace Erdos524.GaussianPolynomialLaw
open MeasureTheory ProbabilityTheory Matrix WithLp
open Erdos524.DiscreteLaplaceGram Erdos524.LaplaceStepKernel Erdos524.LaplaceKernelComparison
open Erdos524.IntegralGramComparison Erdos524.GaussianLinearLaw Erdos524.PolynomialLaplaceGrid

noncomputable def laplaceMatrix {N d : ℕ} (u : Fin d → ℝ) : Matrix (Fin d) (Fin N) ℝ :=
  fun j i => Real.exp (-u j*((i.val+1:ℕ):ℝ)/(N:ℝ))/Real.sqrt N

theorem laplaceMatrix_gram {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ) :
    laplaceMatrix (N := N) u*(laplaceMatrix u)ᵀ=integralGram (fun j => stepLaplace N (u j)) intervalMeasure := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hs := Real.sq_sqrt hNp.le
  ext i j
  rw [step_gram_explicit hN]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,laplaceMatrix]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [div_mul_div_comm,← pow_two,hs,← Real.exp_add]
  congr 2
  ring

theorem gaussian_pi_linear_map {N d : ℕ} (A : Matrix (Fin d) (Fin N) ℝ) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (fun z => A*ᵥz)=
      (multivariateGaussian 0 (A*Aᵀ)).map ofLp := by
  have h := gaussian_linear_map (S := (1 : Matrix (Fin N) (Fin N) ℝ)) (Matrix.PosSemidef.one) A
  rw [Matrix.mul_one,multivariateGaussian_zero_one,← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

theorem gaussian_normalizedLaplace_law {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map (fun z => fun j => normalizedLaplace N z (u j))=
      (multivariateGaussian 0 (integralGram (fun j => stepLaplace N (u j)) intervalMeasure)).map ofLp := by
  have h := gaussian_pi_linear_map (laplaceMatrix (N := N) u)
  rw [laplaceMatrix_gram hN] at h
  have he : (fun z : Fin N → ℝ => laplaceMatrix u*ᵥz)=(fun z => fun j => normalizedLaplace N z (u j)) := by
    funext z j
    simp only [Matrix.mulVec,dotProduct,laplaceMatrix,normalizedLaplace]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    have hex : -u j*((i.val+1:ℕ):ℝ)/(N:ℝ)=-((i.val+1:ℕ):ℝ)/(N:ℝ)*u j := by ring
    rw [hex]
    ring
  rwa [he] at h

end Erdos524.GaussianPolynomialLaw
