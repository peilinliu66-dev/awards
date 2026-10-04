import Erdos524.TruncatedLogTanh
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter

noncomputable def evenPotential (x : ℝ) : ℝ := logTanhPotential |x|

theorem evenPotential_nonneg (x : ℝ) : 0≤evenPotential x := by
  by_cases hx : x=0
  · simp [evenPotential,logTanhPotential,hx]
  · exact (logTanhPotential_pos (abs_pos.mpr hx)).le

theorem integral_evenPotential : (∫ x : ℝ, evenPotential x)=Real.pi^2/2 := by
  unfold evenPotential
  rw [integral_comp_abs,integral_logTanhPotential]
  ring

theorem integrable_evenPotential : Integrable evenPotential := by
  by_contra h
  have he := integral_evenPotential
  rw [integral_undef h] at he
  have hp := sq_pos_of_pos Real.pi_pos
  linarith

theorem integrable_abs_comp_of_half {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x : ℝ => f |x|) := by
  have hpos : IntegrableOn (fun x : ℝ => f |x|) (Ioi 0) := by
    apply hf.congr_fun _ measurableSet_Ioi
    intro x hx
    change f x=f |x|
    rw [abs_of_pos (show 0<x from hx)]
  have hneg : IntegrableOn (fun x : ℝ => f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def,abs_neg,neg_preimage,neg_Iic,neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hpos
  have h := hneg.union hpos
  rwa [Iic_union_Ioi,integrableOn_univ] at h

theorem firstMoment_half_integrable : IntegrableOn (fun x : ℝ => x*logTanhPotential x) (Ioi 0) := by
  have hdom : IntegrableOn (fun x : ℝ => logTanhPotential x+8*Real.exp (-(1/2:ℝ)*x)) (Ioi 0) :=
    integrable_logTanhPotential.add ((integrableOn_exp_mul_Ioi (by norm_num : -(1/2:ℝ)<0) 0).const_mul 8)
  apply hdom.mono' ((measurable_id.mul measurable_logTanhPotential).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hxp : 0<x := hx
  change ‖x*logTanhPotential x‖≤_
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hxp.le (logTanhPotential_pos hxp).le)]
  by_cases hx1 : x≤1
  · have h := mul_le_mul_of_nonneg_right hx1 (logTanhPotential_pos hxp).le
    have he := Real.exp_pos (-(1/2:ℝ)*x)
    linarith
  · have hlog2 : Real.log 2≤x := by have := Real.log_two_lt_d9; linarith
    have hf := mul_le_mul_of_nonneg_left (logTanhPotential_tail hlog2) hxp.le
    have he := Real.add_one_le_exp (x/2)
    have hexp : Real.exp (x/2)*Real.exp (-x)=Real.exp (-(1/2:ℝ)*x) := by
      rw [← Real.exp_add]; congr 1; ring
    have hm := mul_le_mul_of_nonneg_right (show x≤2*Real.exp (x/2) by linarith)
      (show 0≤4*Real.exp (-x) by positivity)
    have hn := (logTanhPotential_pos hxp).le
    nlinarith [hexp]

theorem firstMoment_integrable : Integrable (fun x : ℝ => x*evenPotential x) := by
  have he := integrable_abs_comp_of_half firstMoment_half_integrable
  apply he.mono' ((measurable_id.mul (measurable_logTanhPotential.comp continuous_abs.measurable)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  change ‖x*evenPotential x‖≤ |x| * evenPotential x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (evenPotential_nonneg x)]

theorem integral_firstMoment_zero : (∫ x : ℝ, x*evenPotential x)=0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x*evenPotential x) volume
  simp only [evenPotential,abs_neg,neg_mul,integral_neg] at he
  change -(∫ x : ℝ, x*evenPotential x)=(∫ x : ℝ, x*evenPotential x) at he
  linarith

theorem integral_affine_evenPotential (A B t : ℝ) :
    (∫ s : ℝ, (A-B*s)*evenPotential (s-t)) = (A-B*t)*(Real.pi^2/2) := by
  have he (s : ℝ) : (A-B*s)*evenPotential (s-t) =
      (A-B*t)*evenPotential (s-t)-B*((s-t)*evenPotential (s-t)) := by ring
  simp_rw [he]
  rw [integral_sub ((integrable_evenPotential.comp_sub_right t).const_mul _)
    ((firstMoment_integrable.comp_sub_right t).const_mul _),integral_const_mul,integral_const_mul,
    integral_sub_right_eq_self evenPotential t,
    integral_sub_right_eq_self (fun x : ℝ => x*evenPotential x) t,
    integral_evenPotential,integral_firstMoment_zero]
  ring

end Erdos524.CauchyKernel
