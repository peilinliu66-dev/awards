import Erdos524.PotentialNearIntegral

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter

noncomputable def nearPotential (τ x : ℝ) : ℝ := (Icc (-τ) τ).indicator evenPotential x

theorem nearPotential_nonneg (τ x : ℝ) : 0≤nearPotential τ x := by
  unfold nearPotential
  by_cases h : x ∈ Icc (-τ) τ
  · rw [indicator_of_mem h]; exact evenPotential_nonneg x
  · rw [indicator_of_notMem h]

theorem nearPotential_integrable (τ : ℝ) : Integrable (nearPotential τ) :=
  integrable_evenPotential.indicator measurableSet_Icc

theorem integral_nearPotential (τ : ℝ) :
    (∫ x : ℝ, nearPotential τ x)=2*(∫ x in Ioc 0 τ, logTanhPotential x) := by
  have he : nearPotential τ=(fun x : ℝ => (Iic τ).indicator logTanhPotential |x|) := by
    funext x
    simp only [nearPotential,evenPotential,Set.indicator_apply,mem_Icc,mem_Iic,abs_le]
  rw [he,integral_comp_abs,integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hi : Iic τ ∩ Ioi (0:ℝ)=Ioc 0 τ := by ext x; simp [and_comm]
  rw [hi]

theorem potential_truncation_nonneg {τ x : ℝ} (hτ : 0<τ) (hx : x≠0) :
    0≤evenPotential x-truncatedPotential τ x := by
  unfold evenPotential truncatedPotential
  split_ifs with h
  · exact sub_nonneg.mpr (logTanhPotential_antitone (abs_pos.mpr hx) hτ h)
  · simp

theorem potential_truncation_le_near {τ : ℝ} (hτ : 0<τ) (x : ℝ) :
    evenPotential x-truncatedPotential τ x≤nearPotential τ x := by
  unfold truncatedPotential nearPotential
  by_cases h : |x|≤τ
  · rw [if_pos h,indicator_of_mem (show x∈Icc (-τ) τ from abs_le.mp h)]
    have hp := (logTanhPotential_pos hτ).le
    linarith
  · rw [if_neg h,indicator_of_notMem (by simpa only [mem_Icc,← abs_le] using h)]
    simp [evenPotential]

theorem integrable_affine_evenPotential (A B t : ℝ) :
    Integrable (fun s : ℝ => (A-B*s)*evenPotential (s-t)) := by
  have hf := (integrable_evenPotential.comp_sub_right t).const_mul (A-B*t)
  have hg := (firstMoment_integrable.comp_sub_right t).const_mul B
  convert hf.sub hg using 1
  funext s
  change (A-B*s)*evenPotential (s-t)=(A-B*t)*evenPotential (s-t)-B*((s-t)*evenPotential (s-t))
  ring

end Erdos524.CauchyKernel
