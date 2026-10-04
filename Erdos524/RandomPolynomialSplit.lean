import Erdos524.RandomPolynomialFinite

/-! Exact old/fresh polynomial splitting and the resulting supremum-norm bounds. -/

namespace Erdos524.RandomPolynomialModel

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem polyCM_split (ω : Ω) (n m : ℕ) (x : Interval) :
    polyCM ω (n + m) x = polyCM ω n x + (x : ℝ) ^ n * finitePolyCM (finiteBlock n m ω) x := by
  rw [polyCM_apply, polyCM_apply, finitePolyCM_apply]
  dsimp only [finiteBlock]
  have hs : (∑ i : Fin m, ω (n + i.val) * (x : ℝ) ^ (i.val + 1)) =
      ∑ i ∈ Finset.range m, ω (n + i) * (x : ℝ) ^ (i + 1) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ ω (n + i) * (x : ℝ) ^ (i + 1)) m
  rw [hs, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show n + i + 1 = n + (i + 1) by omega, pow_add]
  ring

theorem finiteNorm_evaluation_bound {n : ℕ} (z : Fin n → ℝ) (x : Interval) :
    |finitePolyCM z x| ≤ finiteNorm z := (finitePolyCM z).norm_coe_le_norm x

theorem norm_polyCM_increment_le (ω : Ω) (n m : ℕ) :
    ‖polyCM ω (n + m) - polyCM ω n‖ ≤ freshNorm n m ω := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  change |polyCM ω (n + m) x - polyCM ω n x| ≤ freshNorm n m ω
  rw [polyCM_split, add_sub_cancel_left, abs_mul, abs_pow]
  have hx : |(x : ℝ)| ≤ 1 := abs_le.mpr x.property
  have hpow : |(x : ℝ)| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  calc
    _ ≤ 1 * |finitePolyCM (finiteBlock n m ω) x| :=
      mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ ≤ freshNorm n m ω := by
      rw [one_mul]
      exact finiteNorm_evaluation_bound _ x

theorem fullNorm_increment_le (ω : Ω) (n m : ℕ) :
    |fullNorm ω (n + m) - fullNorm ω n| ≤ freshNorm n m ω :=
  (abs_norm_sub_norm_le _ _).trans (norm_polyCM_increment_le ω n m)

theorem fullNorm_add_le (ω : Ω) (n m : ℕ) :
    fullNorm ω (n + m) ≤ fullNorm ω n + freshNorm n m ω := by
  have h := (abs_le.mp (fullNorm_increment_le ω n m)).2
  linarith

theorem fullNorm_lower_of_fresh (ω : Ω) (n m : ℕ) :
    fullNorm ω n - freshNorm n m ω ≤ fullNorm ω (n + m) := by
  have h := (abs_le.mp (fullNorm_increment_le ω n m)).1
  linarith

end Erdos524.RandomPolynomialModel
