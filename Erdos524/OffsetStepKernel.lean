import Erdos524.UniformPartition

namespace Erdos524.OffsetStepKernel
open MeasureTheory Filter Set
open Erdos524.ExponentialKernelLipschitz Erdos524.LaplaceKernelComparison
open Erdos524.UniformPartition

noncomputable def offsetStep (N : ℕ) (θ s : ℝ) : ℝ := ((⌊s*(N:ℝ)⌋₊:ℝ)+θ)/(N:ℝ)
noncomputable def offsetLaplace (N : ℕ) (θ u s : ℝ) : ℝ := Real.exp (-u*offsetStep N θ s)

theorem offsetStep_nonneg (N : ℕ) {θ : ℝ} (hθ : 0≤θ) (s : ℝ) : 0≤offsetStep N θ s := by
  unfold offsetStep
  positivity

theorem offsetStep_error {N : ℕ} (hN : 0<N) {θ s : ℝ} (hθ : 0≤θ) (hθ1 : θ≤1) (hs : 0≤s) :
    |offsetStep N θ s-s|≤1/(N:ℝ) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hf := Nat.floor_le (mul_nonneg hs hNp.le)
  have hf' := Nat.lt_floor_add_one (s*(N:ℝ))
  have he : offsetStep N θ s-s=((⌊s*(N:ℝ)⌋₊:ℝ)+θ-s*(N:ℝ))/(N:ℝ) := by unfold offsetStep; field_simp
  rw [he,abs_div,abs_of_pos hNp]
  apply div_le_div_of_nonneg_right _ hNp.le
  rw [abs_le]
  constructor <;> linarith

theorem memLp_offsetLaplace (N : ℕ) {θ u : ℝ} (hθ : 0≤θ) (hu : 0≤u) :
    MemLp (offsetLaplace N θ u) 2 intervalMeasure := by
  have hm : Measurable (offsetLaplace N θ u) := by unfold offsetLaplace offsetStep; fun_prop
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  apply Eventually.of_forall
  intro s
  rw [offsetLaplace,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) (offsetStep_nonneg N hθ s))

theorem offsetLaplace_squared_error {N : ℕ} (hN : 0<N) {θ u : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (hu : 0≤u) :
    (∫ s, (offsetLaplace N θ u s-laplace u s)^2 ∂intervalMeasure)≤u^2/(N:ℝ)^2 := by
  have hi : Integrable (fun s => (offsetLaplace N θ u s-laplace u s)^2) intervalMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs,Pi.sub_apply] using
      ((memLp_offsetLaplace N hθ hu).sub (memLp_laplace_interval hu)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have hpt : ∀ᵐ s ∂intervalMeasure, (offsetLaplace N θ u s-laplace u s)^2≤u^2/(N:ℝ)^2 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with s hs
    have h := exp_kernel_cell_error hu hs.1 (offsetStep_nonneg N hθ s) (offsetStep_error hN hθ hθ1 hs.1)
    simpa only [offsetLaplace,laplace,div_pow,one_pow,mul_one_div] using h
  have h := integral_mono_ae hi (integrable_const (u^2/(N:ℝ)^2)) hpt
  simpa [integral_const,Measure.real,intervalMeasure,Real.volume_Icc] using h

theorem integral_offset_product {N : ℕ} (hN : 0<N) (θ φ u v : ℝ) :
    (∫ s, offsetLaplace N θ u s*offsetLaplace N φ v s ∂intervalMeasure)=
      (∑ i : Fin N, Real.exp (-u*((i:ℝ)+θ)/(N:ℝ))*Real.exp (-v*((i:ℝ)+φ)/(N:ℝ)))/(N:ℝ) := by
  change (∫ s in Icc (0:ℝ) 1, offsetLaplace N θ u s*offsetLaplace N φ v s)=_
  rw [integral_Icc_eq_integral_Ico]
  have hf : (fun s : ℝ => offsetLaplace N θ u s*offsetLaplace N φ v s)=
      (fun s : ℝ => (fun k : ℕ => Real.exp (-u*((k:ℝ)+θ)/(N:ℝ))*Real.exp (-v*((k:ℝ)+φ)/(N:ℝ))) ⌊s*(N:ℝ)⌋₊) := by
    funext s
    unfold offsetLaplace offsetStep
    congr 2 <;> ring
  rw [hf]
  exact integral_floor_step hN (fun k : ℕ => Real.exp (-u*((k:ℝ)+θ)/(N:ℝ))*Real.exp (-v*((k:ℝ)+φ)/(N:ℝ)))

end Erdos524.OffsetStepKernel
