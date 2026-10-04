import Erdos524.SignWalkRecursion

namespace Erdos524.FiniteSignWalk
open MeasureTheory ProbabilityTheory
open Erdos524.SignGaussianMoments Erdos524.SignConcentration

noncomputable def coshFactor (ℓ : ℝ) : ℝ := (Real.exp ℓ+Real.exp (-ℓ))/2

theorem coshFactor_ge_one (ℓ : ℝ) : 1≤coshFactor ℓ := by
  have hp : Real.exp ℓ*Real.exp (-ℓ)=1 := by rw [← Real.exp_add]; simp
  have hs := sq_nonneg (Real.exp ℓ-Real.exp (-ℓ))
  have h1 := Real.exp_pos ℓ
  have h2 := Real.exp_pos (-ℓ)
  unfold coshFactor
  nlinarith

theorem coshFactor_le (ℓ : ℝ) : coshFactor ℓ≤Real.exp (ℓ^2/2) := by
  have h := signLaw_subgaussian.mgf_le ℓ
  rw [mgf,integral_signLaw] at h
  simpa [coshFactor,add_comm] using h

theorem hitProbability_exp_factor (N : ℕ) (t s : ℝ) {ℓ : ℝ} (hℓ : 0≤ℓ) :
    hitProbability N t s≤Real.exp (ℓ*(s-t))*(coshFactor ℓ)^N := by
  induction N generalizing s with
  | zero =>
    rw [hitProbability_zero,pow_zero,mul_one]
    split_ifs with h
    · exact Real.one_le_exp_iff.mpr (mul_nonneg hℓ (sub_nonneg.mpr h))
    · positivity
  | succ N ih =>
    by_cases hs : t≤s
    · rw [hitProbability_of_le hs]
      have he : 1≤Real.exp (ℓ*(s-t)) := Real.one_le_exp_iff.mpr (mul_nonneg hℓ (sub_nonneg.mpr hs))
      have hp : 1≤(coshFactor ℓ)^(N+1) := one_le_pow₀ (coshFactor_ge_one ℓ)
      nlinarith
    · rw [hitProbability_recursion (lt_of_not_ge hs)]
      have h1 := ih (s-1)
      have h2 := ih (s+1)
      have he1 : Real.exp (ℓ*(s-1-t))=Real.exp (ℓ*(s-t))*Real.exp (-ℓ) := by rw [← Real.exp_add]; congr 1; ring
      have he2 : Real.exp (ℓ*(s+1-t))=Real.exp (ℓ*(s-t))*Real.exp ℓ := by rw [← Real.exp_add]; congr 1; ring
      rw [he1] at h1
      rw [he2] at h2
      rw [pow_succ]
      unfold coshFactor at *
      nlinarith

theorem hitProbability_exponential (N : ℕ) (t s : ℝ) {ℓ : ℝ} (hℓ : 0≤ℓ) :
    hitProbability N t s≤Real.exp (ℓ*(s-t)+(N:ℝ)*ℓ^2/2) := by
  have h := hitProbability_exp_factor N t s hℓ
  have hp := pow_le_pow_left₀ (by linarith [coshFactor_ge_one ℓ] : 0≤coshFactor ℓ) (coshFactor_le ℓ) N
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_pos (ℓ*(s-t))).le
  apply h.trans
  apply hm.trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

theorem hitProbability_hoeffding {N : ℕ} (hN : 0<N) {t : ℝ} (ht : 0≤t) :
    hitProbability N t 0≤Real.exp (-t^2/(2*(N:ℝ))) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have h := hitProbability_exponential N t 0 (ℓ := t/(N:ℝ)) (div_nonneg ht hNp.le)
  have he : (t/(N:ℝ))*(0-t)+(N:ℝ)*(t/(N:ℝ))^2/2=-t^2/(2*(N:ℝ)) := by field_simp; ring
  rwa [he] at h

end Erdos524.FiniteSignWalk
