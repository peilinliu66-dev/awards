import Erdos524.ExponentialKernelLipschitz
import Erdos524.LaplaceKernelComparison
import Erdos524.GramGaussianCoupling
import Mathlib.MeasureTheory.Function.Floor

namespace Erdos524.LaplaceStepKernel
open MeasureTheory Filter Set
open Erdos524.ExponentialKernelLipschitz Erdos524.LaplaceKernelComparison
open Erdos524.GramGaussianCoupling

noncomputable def rightStep (N : ℕ) (s : ℝ) : ℝ := (⌊s*(N:ℝ)⌋₊+1:ℝ)/(N:ℝ)
noncomputable def stepLaplace (N : ℕ) (u s : ℝ) : ℝ := Real.exp (-u*rightStep N s)

theorem rightStep_measurable (N : ℕ) : Measurable (rightStep N) := by
  unfold rightStep
  fun_prop

theorem rightStep_nonneg (N : ℕ) (s : ℝ) : 0≤rightStep N s := by unfold rightStep; positivity

theorem rightStep_error {N : ℕ} (hN : 0<N) {s : ℝ} (hs : 0≤s) :
    |rightStep N s-s|≤1/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hf := Nat.floor_le (mul_nonneg hs hNp.le)
  have hf' := Nat.lt_floor_add_one (s*(N:ℝ))
  have hle : s≤rightStep N s := (le_div_iff₀ hNp).mpr hf'.le
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  apply (le_div_iff₀ hNp).mpr
  have he : (rightStep N s-s)*(N:ℝ)=(⌊s*(N:ℝ)⌋₊:ℝ)+1-s*(N:ℝ) := by unfold rightStep; field_simp
  rw [he]
  linarith

theorem memLp_stepLaplace (N : ℕ) {u : ℝ} (hu : 0≤u) : MemLp (stepLaplace N u) 2 intervalMeasure := by
  apply MemLp.of_bound (by unfold stepLaplace; exact ((measurable_const.mul (rightStep_measurable N)).exp).aestronglyMeasurable) 1
  apply Eventually.of_forall
  intro s
  rw [stepLaplace,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (rightStep_nonneg N s))

theorem stepLaplace_squared_error {N : ℕ} (hN : 0<N) {u : ℝ} (hu : 0≤u) :
    (∫ s, (stepLaplace N u s-laplace u s)^2 ∂intervalMeasure)≤u^2/(N:ℝ)^2 := by
  have hi : Integrable (fun s => (stepLaplace N u s-laplace u s)^2) intervalMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using
      ((memLp_stepLaplace N hu).sub (memLp_laplace_interval hu)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hpt : ∀ᵐ s ∂intervalMeasure, (stepLaplace N u s-laplace u s)^2≤u^2/(N:ℝ)^2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    have h := exp_kernel_cell_error hu hs.1 (rightStep_nonneg N s) (rightStep_error hN hs.1)
    simpa only [stepLaplace,laplace,div_pow,one_pow,mul_one_div] using h
  have h := integral_mono_ae hi (integrable_const (u^2/(N:ℝ)^2)) hpt
  simpa [integral_const,Measure.real,intervalMeasure,Real.volume_Icc] using h

theorem step_gaussian_probability_comparison {N d : ℕ} (hN : 0<N) (u : Fin d → ℝ)
    (hu : ∀ j, 0≤u j) {η : ℝ} (hη : 0<η) (r : ℝ) :
    gramBoxProbability (fun j => stepLaplace N (u j)) intervalMeasure r≤
      gramBoxProbability (fun j => laplace (u j)) intervalMeasure (r+η)+
      (∑ j, (u j)^2)/((N:ℝ)^2*η^2) := by
  have h := gram_box_probability_comparison (fun j => stepLaplace N (u j)) (fun j => laplace (u j))
    (fun j => memLp_stepLaplace N (hu j)) (fun j => memLp_laplace_interval (hu j)) hη r
  apply h.trans
  apply add_le_add le_rfl
  calc
    _ ≤ (∑ j, (u j)^2/(N:ℝ)^2)/η^2 := div_le_div_of_nonneg_right
      (Finset.sum_le_sum (fun j _ => stepLaplace_squared_error hN (hu j))) (sq_nonneg η)
    _ = _ := by rw [← Finset.sum_div]; field_simp

end Erdos524.LaplaceStepKernel
