import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic

namespace Erdos524.FourthOrderTaylor
open Set

noncomputable def cubicTaylor (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  f 0+deriv f 0*t+iteratedDeriv 2 f 0*t^2/2+iteratedDeriv 3 f 0*t^3/6

theorem taylorWithin_three_eq {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {t : ℝ} (ht : 0≠t) :
    taylorWithinEval f 3 (uIcc 0 t) 0 t=cubicTaylor f t := by
  have hu := uniqueDiffOn_uIcc ht
  have hx : (0:ℝ)∈uIcc 0 t := left_mem_uIcc
  have hf1 : ContDiff ℝ (1:ℕ) f := hf.of_le (by norm_num)
  have hf2 : ContDiff ℝ (2:ℕ) f := hf.of_le (by norm_num)
  have hf3 : ContDiff ℝ (3:ℕ) f := hf.of_le (by norm_num)
  have h1 := iteratedDerivWithin_eq_iteratedDeriv (n := 1) hu hf1.contDiffAt hx
  have h2 := iteratedDerivWithin_eq_iteratedDeriv (n := 2) hu hf2.contDiffAt hx
  have h3 := iteratedDerivWithin_eq_iteratedDeriv (n := 3) hu hf3.contDiffAt hx
  rw [taylorWithinEval_succ f 2,taylorWithinEval_succ f 1,taylorWithinEval_succ f 0,
    taylor_within_zero_eval,h1,h2,h3]
  norm_num [cubicTaylor,iteratedDeriv_one,smul_eq_mul]
  ring

theorem cubic_remainder_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 4 f) {M : ℝ}
    (hM : ∀ x : ℝ, |iteratedDeriv 4 f x|≤M) (t : ℝ) :
    |f t-cubicTaylor f t|≤M*|t|^4/24 := by
  by_cases ht : 0=t
  · subst t
    simp [cubicTaylor]
  · obtain ⟨ξ,hξ,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) ht hf.contDiffOn
    rw [taylorWithin_three_eq hf ht] at he
    rw [he]
    norm_num only [Nat.reduceAdd,sub_zero,Nat.factorial,abs_div,abs_mul,abs_pow]
    norm_num only
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM ξ) (by positivity)) (by norm_num)

end Erdos524.FourthOrderTaylor
