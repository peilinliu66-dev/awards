import Erdos524.SignGaussianMoments
import Mathlib.Analysis.Real.Pi.Bounds

namespace Erdos524.GaussianTailLower
open MeasureTheory ProbabilityTheory Set Filter

noncomputable def tailConstant : ℝ := Real.exp (-(3/2:ℝ))/Real.sqrt (2*Real.pi)

theorem tailConstant_pos : 0<tailConstant := by unfold tailConstant; positivity

theorem gaussian_density_interval_lower {x y : ℝ} (hx : 1≤x) (hy : y∈Icc x (x+1/x)) :
    tailConstant*Real.exp (-x^2/2)≤gaussianPDFReal 0 1 y := by
  have hxp : 0<x := by linarith
  have hinv0 : 0≤1/x := by positivity
  have hinv1 : 1/x≤1 := (div_le_one hxp).mpr hx
  have hs : (x+1/x)^2=x^2+2+(1/x)^2 := by field_simp; ring
  have hy0 : 0≤y := by linarith [hy.1]
  have hy2 : y^2≤x^2+3 := by
    have hh := pow_le_pow_left₀ hy0 hy.2 2
    rw [hs] at hh
    nlinarith
  have he : tailConstant*Real.exp (-x^2/2)=
      (Real.sqrt (2*Real.pi))⁻¹*Real.exp (-x^2/2-3/2) := by
    unfold tailConstant
    rw [show -x^2/2-3/2=-(3/2:ℝ)+(-x^2/2) by ring,Real.exp_add]
    ring
  rw [he]
  unfold gaussianPDFReal
  simp only [NNReal.coe_one,mul_one,sub_zero]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

theorem gaussian_tail_lower {x : ℝ} (hx : 1≤x) :
    tailConstant*Real.exp (-x^2/2)/x≤(gaussianReal 0 1).real (Ioi x) := by
  have hxp : 0<x := by linarith
  have hinv : 0≤1/x := by positivity
  have hpdf : IntegrableOn (gaussianPDFReal 0 1) (Ioc x (x+1/x)) := (integrable_gaussianPDFReal 0 1).integrableOn
  have hb := integral_mono_ae (integrable_const (tailConstant*Real.exp (-x^2/2))) hpdf (by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with y hy
    exact gaussian_density_interval_lower hx ⟨hy.1.le,hy.2⟩)
  have hlen : x+1/x-x=1/x := by ring
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,hlen,ENNReal.toReal_ofReal hinv,smul_eq_mul] at hb
  have hmeasure : (gaussianReal 0 1).real (Ioc x (x+1/x))=∫ y in Ioc x (x+1/x), gaussianPDFReal 0 1 y := by
    unfold Measure.real
    rw [gaussianReal_apply_eq_integral 0 (by norm_num),ENNReal.toReal_ofReal]
    exact integral_nonneg (gaussianPDFReal_nonneg 0 1)
  calc
    _ = (1/x)*(tailConstant*Real.exp (-x^2/2)) := by ring
    _ ≤ _ := hb
    _ = _ := hmeasure.symm
    _ ≤ _ := measureReal_mono Ioc_subset_Ioi_self

end Erdos524.GaussianTailLower
