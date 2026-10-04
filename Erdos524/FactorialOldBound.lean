import Erdos524.RandomPolynomialTail
import Erdos524.FactorialBlockProbability
import Erdos524.InversePolynomialScale

/-! Almost-sure old-polynomial payment on the factorial mesh. -/

namespace Erdos524.FactorialSparseMesh

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
open Erdos524.RandomPolynomialModel Erdos524.InversePolynomialScale

noncomputable def oldBudget (j : ℕ) : ℝ :=
  Real.sqrt (endpoint j : ℝ) * Real.sqrt (8 * Real.log (j + 2 : ℝ))

theorem oldBudget_pos (j : ℕ) : 0 < oldBudget j := by
  have he : (0 : ℝ) < endpoint j := by exact_mod_cast endpoint_pos j
  have hj : (1 : ℝ) < j + 2 := by have hh : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith
  unfold oldBudget
  exact mul_pos (Real.sqrt_pos.mpr he) (Real.sqrt_pos.mpr (mul_pos (by norm_num) (Real.log_pos hj)))

theorem old_probability_bound (j : ℕ) :
    P.real {ω | oldBudget j ≤ fullNorm ω (endpoint j)} ≤ 4 / (j + 2 : ℝ) ^ 4 := by
  have h := fullNorm_tail (endpoint_pos j) (oldBudget_pos j)
  have he : (0 : ℝ) < endpoint j := by exact_mod_cast endpoint_pos j
  have hj : (0 : ℝ) < j + 2 := by positivity
  have hlog : 0 ≤ Real.log (j + 2 : ℝ) := Real.log_nonneg (by have hh : (0 : ℝ) ≤ j := Nat.cast_nonneg _; linarith)
  have hs : (oldBudget j) ^ 2 = (endpoint j : ℝ) * (8 * Real.log (j + 2 : ℝ)) := by
    unfold oldBudget
    rw [mul_pow, Real.sq_sqrt he.le, Real.sq_sqrt (by positivity)]
  rw [hs] at h
  have hexponent : -((endpoint j : ℝ) * (8 * Real.log (j + 2 : ℝ))) / (2 * (endpoint j : ℝ)) =
      -(4 * Real.log (j + 2 : ℝ)) := by field_simp; ring
  rw [hexponent, Real.exp_neg, show (4 : ℝ) = (4 : ℕ) by norm_num,
    Real.exp_nat_mul, Real.exp_log hj] at h
  simpa only [div_eq_mul_inv, Nat.cast_ofNat] using h

theorem ae_eventual_old_bound :
    ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop, fullNorm ω (endpoint j) ≤ oldBudget j := by
  have hsum : Summable (fun j : ℕ ↦ 4 / (j + 2 : ℝ) ^ 4) := by
    have hs := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (4 : ℕ)))
    have hs' := (summable_nat_add_iff 2).mpr hs
    simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one_div] using hs'.mul_left 4
  have hprob (j : ℕ) : P {ω | oldBudget j ≤ fullNorm ω (endpoint j)} ≤ ENNReal.ofReal (4 / (j + 2 : ℝ) ^ 4) := by
    rw [← ENNReal.ofReal_toReal (by finiteness : P {ω | oldBudget j ≤ fullNorm ω (endpoint j)} ≠ ⊤)]
    exact ENNReal.ofReal_le_ofReal (old_probability_bound j)
  have hfinite : (∑' j, P {ω | oldBudget j ≤ fullNorm ω (endpoint j)}) ≠ ⊤ :=
    ne_of_lt ((ENNReal.tsum_le_tsum hprob).trans_lt hsum.tsum_ofReal_lt_top)
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with j hj
  exact (lt_of_not_ge hj).le

end Erdos524.FactorialSparseMesh
