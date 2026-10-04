import Erdos524.LogTanhPotential
import Erdos524.LayercakeDiscrepancy

namespace Erdos524.CauchyKernel
open Set MeasureTheory

 theorem logTanhPotential_eq_exp_ratio {x : ℝ} (hx : 0<x) :
    logTanhPotential x = Real.log ((Real.exp x+1)/(Real.exp x-1)) := by
  have he : 1<Real.exp x := Real.one_lt_exp_iff.mpr hx
  have ht : Real.tanh (x/2)=(Real.exp x-1)/(Real.exp x+1) := by
    simpa only [Real.exp_zero,sub_zero] using (cauchy_ratio_exp x 0).symm
  unfold logTanhPotential
  rw [ht,Real.log_div (by linarith) (by positivity),
    Real.log_div (by positivity) (by linarith)]
  ring

theorem exp_logTanhPotential {x : ℝ} (hx : 0<x) :
    Real.exp (logTanhPotential x)=(Real.exp x+1)/(Real.exp x-1) := by
  rw [logTanhPotential_eq_exp_ratio hx,Real.exp_log]
  exact div_pos (by positivity) (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))

theorem logTanhPotential_involutive {x : ℝ} (hx : 0<x) :
    logTanhPotential (logTanhPotential x)=x := by
  apply Real.exp_injective
  rw [exp_logTanhPotential (logTanhPotential_pos hx),exp_logTanhPotential hx]
  have he : Real.exp x-1 ≠ 0 := ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx))
  field_simp
  <;> ring

theorem logTanhPotential_strictAnti : StrictAntiOn logTanhPotential (Ioi 0) := by
  intro x hx y hy hxy
  apply lt_of_le_of_ne (logTanhPotential_antitone hx hy hxy.le)
  intro he
  have h := congrArg logTanhPotential he
  rw [logTanhPotential_involutive hy,logTanhPotential_involutive hx] at h
  linarith

theorem le_logTanhPotential_iff {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    y≤logTanhPotential x ↔ x≤logTanhPotential y := by
  constructor
  · intro h
    have he := logTanhPotential_antitone hy (logTanhPotential_pos hx) h
    rwa [logTanhPotential_involutive hx] at he
  · intro h
    have he := logTanhPotential_antitone hx (logTanhPotential_pos hy) h
    rwa [logTanhPotential_involutive hy] at he

noncomputable def truncatedPotential (τ x : ℝ) : ℝ :=
  if |x|≤τ then logTanhPotential τ else logTanhPotential |x|

theorem truncatedPotential_nonneg {τ : ℝ} (hτ : 0<τ) (x : ℝ) : 0≤truncatedPotential τ x := by
  unfold truncatedPotential
  split_ifs with h
  · exact (logTanhPotential_pos hτ).le
  · exact (logTanhPotential_pos (lt_trans hτ (lt_of_not_ge h))).le

theorem truncatedPotential_le {τ : ℝ} (hτ : 0<τ) (x : ℝ) :
    truncatedPotential τ x≤logTanhPotential τ := by
  unfold truncatedPotential
  split_ifs with h
  · rfl
  · exact logTanhPotential_antitone hτ (lt_trans hτ (lt_of_not_ge h)) (le_of_lt (lt_of_not_ge h))

theorem truncatedPotential_level {τ y : ℝ} (hτ : 0<τ) (hy : 0<y)
    (hyτ : y≤logTanhPotential τ) (x : ℝ) :
    y≤truncatedPotential τ x ↔ |x|≤logTanhPotential y := by
  unfold truncatedPotential
  split_ifs with h
  · have he := (le_logTanhPotential_iff hτ hy).mp hyτ
    exact iff_of_true hyτ (h.trans he)
  · exact le_logTanhPotential_iff (lt_trans hτ (lt_of_not_ge h)) hy


theorem measurable_logTanhPotential : Measurable logTanhPotential := by
  unfold logTanhPotential
  simp only [Real.tanh_eq]
  fun_prop

theorem measurable_truncatedPotential (τ : ℝ) : Measurable (truncatedPotential τ) := by
  unfold truncatedPotential
  apply Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) measurable_const
  exact measurable_logTanhPotential.comp continuous_abs.measurable

theorem truncatedPotential_center_level {τ y : ℝ} (hτ : 0<τ) (hy : 0<y)
    (hyτ : y≤logTanhPotential τ) (t : ℝ) :
    {x : ℝ | y≤truncatedPotential τ (x-t)} = Icc (t-logTanhPotential y) (t+logTanhPotential y) := by
  ext x
  rw [mem_setOf_eq,truncatedPotential_level hτ hy hyτ,abs_le,mem_Icc]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

theorem truncatedPotential_integral_discrepancy (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {τ D : ℝ} (hτ : 0<τ) (hD : 0≤D)
    (hinterval : ∀ a b : ℝ, |μ.real (Icc a b)-ν.real (Icc a b)|≤D) (t : ℝ) :
    |(∫ x, truncatedPotential τ (x-t) ∂μ)-(∫ x, truncatedPotential τ (x-t) ∂ν)| ≤
      D*logTanhPotential τ := by
  apply Erdos524.LayercakeDiscrepancy.integral_discrepancy_of_level_bound μ ν
    ((measurable_truncatedPotential τ).comp (measurable_id.sub measurable_const))
    (logTanhPotential_pos hτ).le hD
    (fun x => truncatedPotential_nonneg hτ (x-t))
    (fun x => truncatedPotential_le hτ (x-t))
  intro y hy
  simp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [truncatedPotential_center_level hτ hy.1 hy.2 t]
  exact hinterval _ _

end Erdos524.CauchyKernel
