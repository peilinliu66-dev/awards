import Mathlib.Tactic

namespace Erdos524.PolynomialAbel
open scoped BigOperators

noncomputable def partialSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i
noncomputable def polynomial (a : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ := ∑ i ∈ Finset.range n, a i*x^(i+1)

theorem abel_identity (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    polynomial a n x=(1-x)*(∑ i ∈ Finset.range n, partialSum a (i+1)*x^(i+1))+partialSum a n*x^(n+1) := by
  induction n with
  | zero => simp [polynomial,partialSum]
  | succ n ih =>
    have hp : polynomial a (n+1) x=polynomial a n x+a n*x^(n+1) := by simp [polynomial,Finset.sum_range_succ]
    have hs : partialSum a (n+1)=partialSum a n+a n := by simp [partialSum,Finset.sum_range_succ]
    rw [hp,ih,Finset.sum_range_succ,hs]
    rw [show n+1+1=(n+1)+1 by omega,pow_succ]
    ring

theorem abel_weights (n : ℕ) (x : ℝ) :
    (1-x)*(∑ i ∈ Finset.range n, x^(i+1))+x^(n+1)=x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,pow_succ x (n+1)]
    nlinarith

theorem polynomial_abs_le (a : ℕ → ℝ) (n : ℕ) {x M : ℝ}
    (hx : 0≤x) (hx1 : x≤1) (hM : 0≤M)
    (hS : ∀ k, k≤n → |partialSum a k|≤M) : |polynomial a n x|≤M := by
  rw [abel_identity]
  calc
    _ ≤ |(1-x)*(∑ i ∈ Finset.range n, partialSum a (i+1)*x^(i+1))|+|partialSum a n*x^(n+1)| := abs_add_le _ _
    _ = (1-x)*|∑ i ∈ Finset.range n, partialSum a (i+1)*x^(i+1)|+|partialSum a n| *x^(n+1) := by
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr hx1),abs_of_nonneg (pow_nonneg hx _)]
    _ ≤ (1-x)*(∑ i ∈ Finset.range n, |partialSum a (i+1)*x^(i+1)|)+M*x^(n+1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (sub_nonneg.mpr hx1))
        (mul_le_mul_of_nonneg_right (hS n le_rfl) (pow_nonneg hx _))
    _ ≤ (1-x)*(∑ i ∈ Finset.range n, M*x^(i+1))+M*x^(n+1) := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hx1)
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (pow_nonneg hx _)]
      exact mul_le_mul_of_nonneg_right (hS (i+1) (by have := Finset.mem_range.mp hi; omega)) (pow_nonneg hx _)
    _ = M*x := by rw [← Finset.mul_sum]; nlinarith [abel_weights n x]
    _ ≤ M := by nlinarith

theorem polynomial_at_one (a : ℕ → ℝ) (n : ℕ) : polynomial a n 1=partialSum a n := by
  simp [polynomial,partialSum]

noncomputable def alternating (a : ℕ → ℝ) (i : ℕ) : ℝ := (-1)^(i+1)*a i

theorem polynomial_neg (a : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    polynomial a n (-x)=polynomial (alternating a) n x := by
  unfold polynomial alternating
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_eq_neg_one_mul x,mul_pow]
  ring

theorem polynomial_abs_le_two_walks (a : ℕ → ℝ) (n : ℕ) {x M : ℝ}
    (hx : |x|≤1) (hM : 0≤M)
    (hS : ∀ k, k≤n → |partialSum a k|≤M)
    (hT : ∀ k, k≤n → |partialSum (alternating a) k|≤M) :
    |polynomial a n x|≤M := by
  by_cases h : 0≤x
  · exact polynomial_abs_le a n h ((le_abs_self x).trans hx) hM hS
  · have hn : 0≤-x := by linarith
    have hn1 : -x≤1 := by simpa only [abs_of_neg (lt_of_not_ge h)] using hx
    have hb := polynomial_abs_le (alternating a) n hn hn1 hM hT
    rwa [← polynomial_neg,neg_neg] at hb

end Erdos524.PolynomialAbel
