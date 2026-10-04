import Erdos524.TwoColorKernel

namespace Erdos524.TwoSidedLaplaceKernels
open MeasureTheory Set
open Erdos524.TwoColorKernel Erdos524.OffsetStepKernel Erdos524.LaplaceKernelComparison

noncomputable def exactPair (σ u : ℝ) : Fin 2 × ℝ → ℝ :=
  pairFunction (fun s => σ/Real.sqrt 2*laplace u s) (fun s => 1/Real.sqrt 2*laplace u s)
noncomputable def stepPair (M : ℕ) (σ u : ℝ) : Fin 2 × ℝ → ℝ :=
  pairFunction (fun s => σ/Real.sqrt 2*offsetLaplace M (1/2) u s)
    (fun s => 1/Real.sqrt 2*offsetLaplace M 1 u s)

theorem memLp_exactPair (σ : ℝ) {u : ℝ} (hu : 0≤u) : MemLp (exactPair σ u) 2 colorMeasure :=
  pairFunction_memLp ((memLp_laplace_interval hu).const_mul _) ((memLp_laplace_interval hu).const_mul _)

theorem memLp_stepPair (M : ℕ) (σ : ℝ) {u : ℝ} (hu : 0≤u) : MemLp (stepPair M σ u) 2 colorMeasure :=
  pairFunction_memLp ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1/2) hu).const_mul _)
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1) hu).const_mul _)

theorem exactPair_covariance (σ τ : ℝ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    (∫ z, exactPair σ u z*exactPair τ v z ∂colorMeasure)=
      ((σ*τ+1)/2)*(∫ s, laplace u s*laplace v s ∂intervalMeasure) := by
  unfold exactPair
  rw [integral_pair_product ((memLp_laplace_interval hu).const_mul _) ((memLp_laplace_interval hu).const_mul _)
    ((memLp_laplace_interval hv).const_mul _) ((memLp_laplace_interval hv).const_mul _)]
  have hs : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have he (a b : ℝ) : (fun s => (a/Real.sqrt 2*laplace u s)*(b/Real.sqrt 2*laplace v s))=
      (fun s => (a*b/2)*(laplace u s*laplace v s)) := by
    funext s
    have hn : Real.sqrt (2:ℝ)≠0 := by positivity
    field_simp
    rw [hs]
    ring
  rw [he σ τ,he 1 1,integral_const_mul,integral_const_mul]
  ring

theorem stepPair_squared_error {M : ℕ} (hM : 0<M) {σ u : ℝ} (hσ : σ^2=1) (hu : 0≤u) :
    (∫ z, (stepPair M σ u z-exactPair σ u z)^2 ∂colorMeasure)≤u^2/(M:ℝ)^2 := by
  let a : ℝ → ℝ := fun s => σ/Real.sqrt 2*(offsetLaplace M (1/2) u s-laplace u s)
  let b : ℝ → ℝ := fun s => 1/Real.sqrt 2*(offsetLaplace M 1 u s-laplace u s)
  have ha : MemLp a 2 intervalMeasure :=
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1/2) hu).sub (memLp_laplace_interval hu)).const_mul _
  have hb : MemLp b 2 intervalMeasure :=
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1) hu).sub (memLp_laplace_interval hu)).const_mul _
  have he : (fun z => (stepPair M σ u z-exactPair σ u z)^2)=(fun z => pairFunction a b z*pairFunction a b z) := by
    funext z
    simp only [stepPair,exactPair,pairFunction,a,b]
    split_ifs <;> ring
  rw [he,integral_pair_product ha hb ha hb]
  have hs : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2:ℝ)≠0 := by positivity
  have heA : (fun s => a s*a s)=(fun s => (1/2:ℝ)*(offsetLaplace M (1/2) u s-laplace u s)^2) := by
    funext s
    dsimp only [a]
    rw [← pow_two,mul_pow,div_pow,hσ,hs]
  have heB : (fun s => b s*b s)=(fun s => (1/2:ℝ)*(offsetLaplace M 1 u s-laplace u s)^2) := by
    funext s
    dsimp only [b]
    rw [← pow_two,mul_pow,div_pow,hs]
    norm_num
  rw [heA,heB,integral_const_mul,integral_const_mul]
  have hA := offsetLaplace_squared_error hM (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1) hu
  have hB := offsetLaplace_squared_error hM (by norm_num : (0:ℝ)≤1) le_rfl hu
  linarith

end Erdos524.TwoSidedLaplaceKernels
