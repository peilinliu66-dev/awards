import Erdos524.MatchedMomentComparison
import Mathlib.Probability.Distributions.Gaussian.Real

namespace Erdos524.SignGaussianMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable def signLaw : Measure ℝ := (1/2:ℝ≥0∞) • Measure.dirac (-1)+(1/2:ℝ≥0∞) • Measure.dirac 1

instance signLaw_probability : IsProbabilityMeasure signLaw := by
  constructor
  norm_num [signLaw,Measure.add_apply,Measure.smul_apply,Measure.dirac_apply]
  rw [← two_mul,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

theorem integrable_signLaw (f : ℝ → ℝ) : Integrable f signLaw := by
  have h1 : Integrable f (Measure.dirac (-1)) := integrable_dirac (by finiteness)
  have h2 : Integrable f (Measure.dirac 1) := integrable_dirac (by finiteness)
  exact (h1.smul_measure (by finiteness)).add_measure (h2.smul_measure (by finiteness))

theorem integral_signLaw (f : ℝ → ℝ) : (∫ x, f x ∂signLaw)=(f (-1)+f 1)/2 := by
  have h1 : Integrable f (Measure.dirac (-1)) := integrable_dirac (by finiteness)
  have h2 : Integrable f (Measure.dirac 1) := integrable_dirac (by finiteness)
  unfold signLaw
  rw [integral_add_measure (h1.smul_measure (by finiteness)) (h2.smul_measure (by finiteness)),
    integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac]
  norm_num
  ring

theorem integrable_gaussian_pow (k : ℕ) : Integrable (fun x : ℝ => x^k) (gaussianReal 0 1) := by
  by_cases hk : k=0
  · subst k; simpa only [pow_zero] using integrable_const (1:ℝ)
  · have hm := memLp_id_gaussianReal' (μ := 0) (v := 1) (k:ℝ≥0∞) (by finiteness)
    have hi := hm.integrable_norm_pow hk
    apply (integrable_norm_iff (show AEStronglyMeasurable (fun x : ℝ => x^k) (gaussianReal 0 1) by fun_prop)).mp
    simpa only [Real.norm_eq_abs,id_eq,pow_abs] using hi

noncomputable def mgfBase (t : ℝ) : ℝ := Real.exp (t^2/2)
noncomputable def mgfFirst (t : ℝ) : ℝ := t*mgfBase t
noncomputable def mgfSecond (t : ℝ) : ℝ := (t^2+1)*mgfBase t
noncomputable def mgfThird (t : ℝ) : ℝ := (t^3+3*t)*mgfBase t
noncomputable def mgfFourth (t : ℝ) : ℝ := (t^4+6*t^2+3)*mgfBase t

theorem mgfBase_hasDerivAt (t : ℝ) : HasDerivAt mgfBase (mgfFirst t) t := by
  convert (((hasDerivAt_id t).pow 2).div_const 2).exp using 1
  · funext s; rfl
  · unfold mgfFirst mgfBase
    simp only [id_eq,Pi.pow_apply]
    ring

theorem mgfFirst_hasDerivAt (t : ℝ) : HasDerivAt mgfFirst (mgfSecond t) t := by
  convert (hasDerivAt_id t).mul (mgfBase_hasDerivAt t) using 1
  · funext s; rfl
  · unfold mgfFirst mgfSecond
    simp only [id_eq,Pi.pow_apply]
    ring

theorem mgfSecond_hasDerivAt (t : ℝ) : HasDerivAt mgfSecond (mgfThird t) t := by
  convert (((hasDerivAt_id t).pow 2).add_const 1).mul (mgfBase_hasDerivAt t) using 1
  · funext s; rfl
  · unfold mgfFirst mgfThird
    simp only [id_eq,Pi.pow_apply]
    ring

theorem mgfThird_hasDerivAt (t : ℝ) : HasDerivAt mgfThird (mgfFourth t) t := by
  convert (((hasDerivAt_id t).pow 3).add ((hasDerivAt_id t).const_mul 3)).mul (mgfBase_hasDerivAt t) using 1
  · funext s
    dsimp only [mgfThird,Pi.add_apply,Pi.mul_apply,Pi.pow_apply,id_eq]
  · unfold mgfFirst mgfFourth
    simp only [id_eq,Pi.pow_apply,Pi.add_apply,Pi.mul_apply]
    ring

theorem gaussian_moment_one : (∫ x : ℝ, x^1 ∂gaussianReal 0 1)=0 := by
  simpa only [pow_one] using (integral_id_gaussianReal (μ := 0) (v := 1))

theorem gaussian_moment_two : (∫ x : ℝ, x^2 ∂gaussianReal 0 1)=1 := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at he
  simpa only [sub_zero,NNReal.coe_one] using he

theorem gaussian_moment_three : (∫ x : ℝ, x^3 ∂gaussianReal 0 1)=0 := by
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 3
  simp only [Pi.pow_apply] at hm
  rw [← hm,mgf_fun_id_gaussianReal]
  simp only [zero_mul,zero_add,NNReal.coe_one,one_mul]
  change iteratedDeriv 3 mgfBase 0=0
  have h1 : deriv mgfBase=mgfFirst := funext (fun t => (mgfBase_hasDerivAt t).deriv)
  have h2 : deriv mgfFirst=mgfSecond := funext (fun t => (mgfFirst_hasDerivAt t).deriv)
  have h3 : deriv mgfSecond=mgfThird := funext (fun t => (mgfSecond_hasDerivAt t).deriv)
  rw [iteratedDeriv_succ (n := 2),iteratedDeriv_succ (n := 1),iteratedDeriv_one,h1,h2,h3]
  norm_num [mgfThird]

theorem gaussian_moment_four : (∫ x : ℝ, x^4 ∂gaussianReal 0 1)=3 := by
  have hm := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 4
  simp only [Pi.pow_apply] at hm
  rw [← hm,mgf_fun_id_gaussianReal]
  simp only [zero_mul,zero_add,NNReal.coe_one,one_mul]
  change iteratedDeriv 4 mgfBase 0=3
  have h1 : deriv mgfBase=mgfFirst := funext (fun t => (mgfBase_hasDerivAt t).deriv)
  have h2 : deriv mgfFirst=mgfSecond := funext (fun t => (mgfFirst_hasDerivAt t).deriv)
  have h3 : deriv mgfSecond=mgfThird := funext (fun t => (mgfSecond_hasDerivAt t).deriv)
  have h4 : deriv mgfThird=mgfFourth := funext (fun t => (mgfThird_hasDerivAt t).deriv)
  rw [iteratedDeriv_succ (n := 3),iteratedDeriv_succ (n := 2),
    iteratedDeriv_succ (n := 1),iteratedDeriv_one,h1,h2,h3,h4]
  norm_num [mgfFourth,mgfBase]

theorem sign_gaussian_first_three (k : ℕ) (hk : k≤3) :
    (∫ x : ℝ, x^k ∂signLaw)=(∫ x : ℝ, x^k ∂gaussianReal 0 1) := by
  interval_cases k
  · simp
  · rw [integral_signLaw,gaussian_moment_one]; norm_num
  · rw [integral_signLaw,gaussian_moment_two]; norm_num
  · rw [integral_signLaw,gaussian_moment_three]; norm_num

end Erdos524.SignGaussianMoments
