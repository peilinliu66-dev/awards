import Erdos524.LogTanhPotential

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem log_tanh_potential_abs (d : ℝ) :
    Real.log (Real.tanh (d/2)) = -logTanhPotential |d| := by
  unfold logTanhPotential
  rw [neg_neg]
  by_cases hd : 0 ≤ d
  · rw [abs_of_nonneg hd]
  · rw [abs_of_neg (lt_of_not_ge hd), neg_div, Real.tanh_neg, Real.log_neg_eq_log]

theorem inverse_diagonal_exp_log {n : ℕ} (t : Fin (n+1) → ℝ)
    (ht : Function.Injective t) (i : Fin (n+1)) :
    Real.log ((normalized (fun j => Real.exp (t j)))⁻¹ i i) =
      Real.log 2 + 2 * ∑ k : Fin n, logTanhPotential |t (i.succAbove k)-t i| := by
  have hinj : Function.Injective (fun j => Real.exp (t j)) := Real.exp_injective.comp ht
  rw [normalized_inverse_diagonal _ (fun j => Real.exp_pos _) hinj i]
  simp_rw [cauchy_ratio_exp]
  have hne (k : Fin n) : Real.tanh ((t (i.succAbove k)-t i)/2) ≠ 0 := by
    rw [← cauchy_ratio_exp]
    apply div_ne_zero
    · exact sub_ne_zero.mpr (fun h => Fin.succAbove_ne i k (hinj h))
    · positivity
  rw [Real.log_div (by norm_num) (pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun k _ => hne k))),
    Real.log_pow, Real.log_prod (fun k _ => hne k)]
  simp_rw [log_tanh_potential_abs, Finset.sum_neg_distrib]
  ring

theorem inverse_diagonal_exp_eq {n : ℕ} (t : Fin (n+1) → ℝ)
    (ht : Function.Injective t) (i : Fin (n+1)) :
    (normalized (fun j => Real.exp (t j)))⁻¹ i i =
      2 * Real.exp (2 * ∑ k : Fin n, logTanhPotential |t (i.succAbove k)-t i|) := by
  have hinj : Function.Injective (fun j => Real.exp (t j)) := Real.exp_injective.comp ht
  have hp : 0 < (normalized (fun j => Real.exp (t j)))⁻¹ i i := by
    rw [normalized_inverse_diagonal _ (fun j => Real.exp_pos _) hinj i]
    apply div_pos (by norm_num)
    apply sq_pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro k _
    exact div_ne_zero (sub_ne_zero.mpr (fun h => Fin.succAbove_ne i k (hinj h)))
      (by positivity)
  have he := congrArg Real.exp (inverse_diagonal_exp_log t ht i)
  rw [Real.exp_log hp, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)] at he
  exact he

end Erdos524.CauchyKernel
