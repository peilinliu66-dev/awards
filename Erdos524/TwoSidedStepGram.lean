import Erdos524.TwoSidedGaussianLimit

namespace Erdos524.TwoSidedStepGram
open MeasureTheory
open Erdos524.TwoColorKernel Erdos524.TwoSidedLaplaceKernels
open Erdos524.OffsetStepKernel Erdos524.LaplaceKernelComparison

theorem sum_range_even_odd (f : ℕ → ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range (2*M), f i)=(∑ k ∈ Finset.range M, f (2*k))+(∑ k ∈ Finset.range M, f (2*k+1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2*(M+1)=2*M+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ,Finset.sum_range_succ]
    ring

theorem stepPair_covariance {M : ℕ} (hM : 0<M) (σ τ : ℝ) {u v : ℝ} (hu : 0≤u) (hv : 0≤v) :
    (∫ z, stepPair M σ u z*stepPair M τ v z ∂colorMeasure)=
      (σ*τ*(∑ k : Fin M, Real.exp (-u*((k:ℝ)+1/2)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1/2)/(M:ℝ)))+
      (∑ k : Fin M, Real.exp (-u*((k:ℝ)+1)/(M:ℝ))*Real.exp (-v*((k:ℝ)+1)/(M:ℝ))))/(2*(M:ℝ)) := by
  unfold stepPair
  rw [integral_pair_product ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1/2) hu).const_mul _)
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1) hu).const_mul _)
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1/2) hv).const_mul _)
    ((memLp_offsetLaplace M (by norm_num : (0:ℝ)≤1) hv).const_mul _)]
  have hs : Real.sqrt (2:ℝ)^2=2 := Real.sq_sqrt (by norm_num)
  have he (a b : ℝ) (f g : ℝ → ℝ) :
      (fun s => (a/Real.sqrt 2*f s)*(b/Real.sqrt 2*g s))=(fun s => (a*b/2)*(f s*g s)) := by
    funext s
    have hn : Real.sqrt (2:ℝ)≠0 := by positivity
    field_simp
    rw [hs]
    ring
  rw [he σ τ,he 1 1,integral_const_mul,integral_const_mul,
    integral_offset_product hM,integral_offset_product hM]
  ring

end Erdos524.TwoSidedStepGram
