import Erdos524.EvenLogTanhIntegrals

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter

noncomputable def absoluteTail (G : ℝ) : Set ℝ := {x | G≤|x|}

theorem measurableSet_absoluteTail (G : ℝ) : MeasurableSet (absoluteTail G) :=
  measurableSet_le measurable_const continuous_abs.measurable

theorem integrable_evenExp {c : ℝ} (hc : 0<c) : Integrable (fun x : ℝ => Real.exp (-c*|x|)) :=
  integrable_abs_comp_of_half (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0)

theorem integral_evenExp_tail {c G : ℝ} (hc : 0<c) (hG : 0<G) :
    (∫ x in absoluteTail G, Real.exp (-c*|x|)) = (2/c)*Real.exp (-c*G) := by
  rw [← integral_indicator (measurableSet_absoluteTail G)]
  have he : (absoluteTail G).indicator (fun x : ℝ => Real.exp (-c*|x|)) =
      (fun x : ℝ => (Ici G).indicator (fun u => Real.exp (-c*u)) |x|) := by
    funext x
    simp only [Set.indicator_apply,absoluteTail,mem_setOf_eq,mem_Ici]
  rw [he,integral_comp_abs,integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hi : Ici G ∩ Ioi (0:ℝ)=Ici G := inter_eq_left.mpr (fun _ hx => lt_of_lt_of_le hG hx)
  rw [hi,integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hc)]
  ring

theorem firstMoment_pointwise_tail {x : ℝ} (hx : Real.log 2≤x) :
    x*logTanhPotential x≤8*Real.exp (-(1/2:ℝ)*x) := by
  have hxp : 0<x := lt_of_lt_of_le (Real.log_pos (by norm_num)) hx
  have hf := mul_le_mul_of_nonneg_left (logTanhPotential_tail hx) hxp.le
  have he := Real.add_one_le_exp (x/2)
  have hexp : Real.exp (x/2)*Real.exp (-x)=Real.exp (-(1/2:ℝ)*x) := by
    rw [← Real.exp_add]; congr 1; ring
  have hm := mul_le_mul_of_nonneg_right (show x≤2*Real.exp (x/2) by linarith)
    (show 0≤4*Real.exp (-x) by positivity)
  nlinarith [hexp]

theorem absolute_firstMoment_integrable : Integrable (fun x : ℝ => |x| * evenPotential x) := by
  convert firstMoment_integrable.norm using 1
  funext x
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (evenPotential_nonneg x)]

theorem linear_potential_tail_bound {C B G : ℝ} (hC : 0≤C) (hB : 0≤B) (hG : Real.log 2≤G) :
    (∫ x in absoluteTail G, (C+B*|x|)*evenPotential x) ≤
      8*C*Real.exp (-G)+32*B*Real.exp (-(1/2:ℝ)*G) := by
  have hGp : 0<G := lt_of_lt_of_le (Real.log_pos (by norm_num)) hG
  have hf : Integrable (fun x : ℝ => (C+B*|x|)*evenPotential x) := by
    convert (integrable_evenPotential.const_mul C).add (absolute_firstMoment_integrable.const_mul B) using 1
    funext x
    change _=C*evenPotential x+B*(|x| * evenPotential x)
    ring
  have hg : Integrable (fun x : ℝ => 4*C*Real.exp (-|x|)+8*B*Real.exp (-(1/2:ℝ)*|x|)) := by
    have h1 := (integrable_evenExp (by norm_num : (0:ℝ)<1)).const_mul (4*C)
    have h2 := (integrable_evenExp (by norm_num : (0:ℝ)<1/2)).const_mul (8*B)
    convert h1.add h2 using 1
    funext x
    simp only [Pi.add_apply,neg_mul,one_mul]
  have hbound : (∫ x in absoluteTail G, (C+B*|x|)*evenPotential x) ≤
      ∫ x in absoluteTail G, (4*C*Real.exp (-|x|)+8*B*Real.exp (-(1/2:ℝ)*|x|)) := by
    apply integral_mono_ae hf.integrableOn hg.integrableOn
    filter_upwards [ae_restrict_mem (measurableSet_absoluteTail G)] with x hx
    have hl : Real.log 2≤|x| := hG.trans hx
    have h1 := mul_le_mul_of_nonneg_left (logTanhPotential_tail hl) hC
    have h2 := mul_le_mul_of_nonneg_left (firstMoment_pointwise_tail hl) hB
    unfold evenPotential
    nlinarith
  have heval : (∫ x in absoluteTail G, (4*C*Real.exp (-|x|)+8*B*Real.exp (-(1/2:ℝ)*|x|))) =
      8*C*Real.exp (-G)+32*B*Real.exp (-(1/2:ℝ)*G) := by
    have hint1 : IntegrableOn (fun x : ℝ => 4*C*Real.exp (-|x|)) (absoluteTail G) := by
      convert ((integrable_evenExp (by norm_num : (0:ℝ)<1)).const_mul (4*C)).integrableOn using 1
      funext x
      simp only [neg_mul,one_mul]
    rw [integral_add hint1
      (((integrable_evenExp (by norm_num : (0:ℝ)<1/2)).const_mul (8*B)).integrableOn),
      integral_const_mul,integral_const_mul]
    have h1 := integral_evenExp_tail (by norm_num : (0:ℝ)<1) hGp
    simp only [neg_mul,one_mul,div_one] at h1
    rw [h1,integral_evenExp_tail (by norm_num : (0:ℝ)<1/2) hGp]
    ring
  rwa [heval] at hbound

end Erdos524.CauchyKernel
