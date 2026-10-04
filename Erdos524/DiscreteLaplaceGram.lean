import Erdos524.UniformPartition

namespace Erdos524.DiscreteLaplaceGram
open MeasureTheory Set
open Erdos524.UniformPartition Erdos524.LaplaceStepKernel Erdos524.LaplaceKernelComparison
open Erdos524.IntegralGramComparison

theorem integral_step_product {N : ℕ} (hN : 0<N) (u v : ℝ) :
    (∫ s, stepLaplace N u s*stepLaplace N v s ∂intervalMeasure)=
      (∑ i : Fin N, Real.exp (-u*((i.val+1:ℕ):ℝ)/(N:ℝ))*Real.exp (-v*((i.val+1:ℕ):ℝ)/(N:ℝ)))/(N:ℝ) := by
  change (∫ s in Icc (0:ℝ) 1, stepLaplace N u s*stepLaplace N v s)=_
  rw [integral_Icc_eq_integral_Ico]
  have hf : (fun s : ℝ => stepLaplace N u s*stepLaplace N v s)=
      (fun s : ℝ => (fun k : ℕ => Real.exp (-u*((k+1:ℕ):ℝ)/(N:ℝ))*Real.exp (-v*((k+1:ℕ):ℝ)/(N:ℝ))) ⌊s*(N:ℝ)⌋₊) := by
    funext s
    unfold stepLaplace rightStep
    push_cast
    congr 2 <;> ring
  rw [hf]
  exact integral_floor_step hN (fun k : ℕ => Real.exp (-u*((k+1:ℕ):ℝ)/(N:ℝ))*Real.exp (-v*((k+1:ℕ):ℝ)/(N:ℝ)))

theorem step_gram_explicit {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ) (i j : Fin d) :
    integralGram (fun j => stepLaplace N (u j)) intervalMeasure i j=
      (∑ k : Fin N, Real.exp (-(u i+u j)*((k.val+1:ℕ):ℝ)/(N:ℝ)))/(N:ℝ) := by
  rw [integralGram,integral_step_product hN]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Real.exp_add]
  congr 1
  ring

end Erdos524.DiscreteLaplaceGram
