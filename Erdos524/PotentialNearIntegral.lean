import Erdos524.EvenLogTanhIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos524.CauchyKernel
open Set MeasureTheory Filter

theorem near_integral_bound {τ : ℝ} (hτ : 0<τ) (hτ1 : τ≤1) :
    (∫ x in Ioc 0 τ, logTanhPotential x) ≤ τ*(Real.log 4-Real.log τ+1) := by
  have hf : IntegrableOn logTanhPotential (Ioc 0 τ) :=
    integrable_logTanhPotential.mono_set Ioc_subset_Ioi_self
  have hg : IntervalIntegrable (fun x : ℝ => Real.log 4-Real.log x) volume 0 τ :=
    intervalIntegrable_const.sub intervalIntegral.intervalIntegrable_log'
  have hgset := (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mp hg
  have hbound : (∫ x in Ioc 0 τ, logTanhPotential x) ≤
      ∫ x in Ioc 0 τ, (Real.log 4-Real.log x) := by
    apply integral_mono_ae hf hgset
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have he := logTanhPotential_near_zero hx.1 (hx.2.trans hτ1)
    rwa [Real.log_div (by norm_num) (ne_of_gt hx.1)] at he
  have heval : (∫ x in Ioc (0:ℝ) τ, (Real.log 4-Real.log x)) = τ*(Real.log 4-Real.log τ+1) := by
    rw [← intervalIntegral.integral_of_le hτ.le,
      intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_log',
      intervalIntegral.integral_const,integral_log]
    simp only [sub_zero,smul_eq_mul,Real.log_zero,zero_mul,sub_zero,add_zero]
    ring
  rwa [heval] at hbound

theorem scaled_near_integral_bound {M : ℝ} (hM : 1≤M) :
    2*M*(∫ x in Ioc 0 (1/M), logTanhPotential x) ≤ 2*Real.log (4*M)+2 := by
  have hMp : 0<M := by linarith
  have ht : 0<1/M := by positivity
  have ht1 : 1/M≤1 := (div_le_one hMp).mpr hM
  have he := mul_le_mul_of_nonneg_left (near_integral_bound ht ht1) (show 0≤2*M by positivity)
  have hr : 2*M*((1/M)*(Real.log 4-Real.log (1/M)+1)) = 2*Real.log (4*M)+2 := by
    rw [Real.log_div (by norm_num) (ne_of_gt hMp),Real.log_one,
      Real.log_mul (by norm_num) (ne_of_gt hMp)]
    field_simp
    <;> ring
  rwa [hr] at he

end Erdos524.CauchyKernel
