import Erdos524.CauchyInterpolation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace Erdos524.CauchyKernel
open scoped BigOperators

theorem sqrt_exp_half (t : ℝ) : Real.sqrt (Real.exp t) = Real.exp (t / 2) := by
  apply (Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos t).le (Real.exp_pos _).le).mpr
  rw [← Real.exp_add]
  congr 1
  ring

theorem normalizedKernel_exp (s t : ℝ) :
    normalizedKernel (Real.exp s) (Real.exp t) =
      1 / (2 * Real.cosh ((s - t) / 2)) := by
  have h1 : Real.exp ((s - t) / 2) * Real.exp ((s + t) / 2) = Real.exp s := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-((s - t) / 2)) * Real.exp ((s + t) / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.sqrt (Real.exp s) * Real.sqrt (Real.exp t) = Real.exp ((s + t) / 2) := by
    rw [sqrt_exp_half, sqrt_exp_half, ← Real.exp_add]; congr 1; ring
  have hpos : Real.exp s + Real.exp t ≠ 0 := ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have hc : Real.cosh ((s - t) / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  unfold normalizedKernel
  rw [mul_comm (Real.sqrt (Real.exp s)), mul_assoc, h3]
  field_simp
  rw [Real.cosh_eq]
  nlinarith [h1, h2]

theorem cauchy_ratio_exp (s t : ℝ) :
    (Real.exp s - Real.exp t) / (Real.exp s + Real.exp t) =
      Real.tanh ((s - t) / 2) := by
  have h1 : Real.exp ((s - t) / 2) * Real.exp ((s + t) / 2) = Real.exp s := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (-((s - t) / 2)) * Real.exp ((s + t) / 2) = Real.exp t := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.tanh_eq]
  have hp : Real.exp s + Real.exp t ≠ 0 := ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  have hq : Real.exp ((s-t)/2) + Real.exp (-((s-t)/2)) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  apply (div_eq_div_iff hp hq).mpr
  rw [← h1, ← h2]
  ring

theorem blaschke_exp {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    blaschke (fun i => Real.exp (x i)) (Real.exp t) =
      ∏ i, Real.tanh ((t - x i) / 2) := by
  simp only [blaschke, numerator, denominator, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact cauchy_ratio_exp t (x i)


theorem one_sub_sech_le_half_sq (z : ℝ) :
    1 - 1 / Real.cosh z ≤ z ^ 2 / 2 := by
  have he := Real.add_one_le_exp (-(z ^ 2 / 2))
  have hi : Real.exp (-(z ^ 2 / 2)) ≤ 1 / Real.cosh z := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.cosh_pos z) (Real.cosh_le_exp_half_sq z)
  linarith

theorem normalized_exp_increment_le (s t : ℝ) :
    normalizedKernel (Real.exp s) (Real.exp s) +
      normalizedKernel (Real.exp t) (Real.exp t) -
      2 * normalizedKernel (Real.exp s) (Real.exp t) ≤ (s-t)^2 / 8 := by
  simp only [normalizedKernel_exp, sub_self, zero_div, Real.cosh_zero]
  have h := one_sub_sech_le_half_sq ((s-t)/2)
  convert h using 1 <;> ring


theorem normalizedWeight_kernel_product {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) (j : Fin n) {v : ℝ} (hv : 0 < v) :
    normalizedWeight x j v = 2 * normalizedKernel v (x j) *
      ∏ k ∈ Finset.univ.erase j,
        (((v-x k)/(v+x k)) / ((x j-x k)/(x j+x k))) := by
  unfold normalizedWeight
  rw [regressionWeight_product x hx j hv]
  have hp : Real.sqrt v / Real.sqrt (x j) * (2*x j/(v+x j)) =
      2 * normalizedKernel v (x j) := by
    have hs := Real.sq_sqrt (hx j).le
    have hsn : Real.sqrt (x j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hx j))
    unfold normalizedKernel
    field_simp
    rw [hs]
  rw [← mul_assoc, hp]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]

theorem normalizedWeight_exp {n : ℕ} (x : Fin n → ℝ) (j : Fin n) (t : ℝ) :
    normalizedWeight (fun i => Real.exp (x i)) j (Real.exp t) =
      (1 / Real.cosh ((t-x j)/2)) *
        ∏ k ∈ Finset.univ.erase j,
          (Real.tanh ((t-x k)/2) / Real.tanh ((x j-x k)/2)) := by
  rw [normalizedWeight_kernel_product _ (fun i => Real.exp_pos _) j (Real.exp_pos t),
    normalizedKernel_exp]
  simp_rw [cauchy_ratio_exp]
  congr 1
  ring

end Erdos524.CauchyKernel
