import Erdos524.DenseVarianceBudget
import Erdos524.RandomPolynomialMaximal
import Mathlib.Analysis.PSeries
import Mathlib.Probability.BorelCantelli

/-! Almost-sure simultaneous control of every fresh prefix between adaptive mesh points. -/

namespace Erdos524.DenseMeshIncrement

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Erdos524.AdaptiveDyadicMesh Erdos524.RandomPolynomialModel
open Erdos524.InversePolynomialScale Erdos524.InverseSmallBallMargins

noncomputable def capacity (k : ℕ) : ℕ := 2 * (2 ^ k / count k + 1)
noncomputable def threshold (ε : ℝ) (k j : ℕ) : ℝ := ε * normalizer (point k j : ℝ)
noncomputable def badEvent (ε : ℝ) (k : ℕ) : Set Ω :=
  ⋃ j : Fin (count k), {ω | ∃ n, point k j ≤ n ∧ n ≤ point k (j.val + 1) ∧
    threshold ε k j ≤ |fullNorm ω n - fullNorm ω (point k j)|}

theorem capacity_pos (k : ℕ) : 0 < capacity k := by unfold capacity; positivity

theorem capacity_ratio (k j : ℕ) (hk : count k ≤ 2 ^ k) :
    (capacity k : ℝ) * (count k : ℝ) ≤ 2 * (point k j : ℝ) := by
  have hdiv := Nat.div_mul_le_self (2 ^ k) (count k)
  have hp := point_lower k j
  have hh : capacity k * count k ≤ 2 * point k j := by unfold capacity; nlinarith
  exact_mod_cast hh

theorem eventually_one_increment_bound {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ j, j < count k →
      P.real {ω | ∃ n, point k j ≤ n ∧ n ≤ point k (j + 1) ∧
        threshold ε k j ≤ |fullNorm ω n - fullNorm ω (point k j)|} ≤
      4 * Real.exp (-(ε ^ 2 / 4) * Real.exp (exponent k / 2)) := by
  filter_upwards [eventually_count_le_dyadic, eventually_count_delta_sq, eventually_inverseLog_band] with k hk hδ hL
  intro j hj
  have hband := hL (point k j) (point_lower k j) (point_upper k j (by omega))
  have hd : 0 < delta (point k j : ℝ) := (inverseRadius_spec hband.1).1
  have hp : (0 : ℝ) < point k j := by
    have hh := point_lower k j
    have hpow : 0 < 2 ^ k := pow_pos (by norm_num) _
    exact_mod_cast (show 0 < point k j by omega)
  have ht : 0 < threshold ε k j := by unfold threshold normalizer; positivity
  have hcap : (0 : ℝ) < capacity k := by exact_mod_cast capacity_pos k
  have hstep : point k (j + 1) ≤ point k j + capacity k := Erdos524.DyadicMesh.point_step_bound _ _ _
  have hsub : {ω : Ω | ∃ n, point k j ≤ n ∧ n ≤ point k (j + 1) ∧
      threshold ε k j ≤ |fullNorm ω n - fullNorm ω (point k j)|} ⊆
      {ω | ∃ n, point k j ≤ n ∧ n ≤ point k j + capacity k ∧
        threshold ε k j ≤ |fullNorm ω n - fullNorm ω (point k j)|} := by
    rintro ω ⟨n, hn, hn', hb⟩
    exact ⟨n, hn, hn'.trans hstep, hb⟩
  have hprob := (measureReal_mono (μ := P) hsub).trans
    (fullNorm_increment_maximal_tail (point k j) (capacity_pos k) ht)
  have hsq : (threshold ε k j) ^ 2 = ε ^ 2 * (point k j : ℝ) * (delta (point k j : ℝ)) ^ 2 := by
    unfold threshold normalizer
    rw [mul_pow, mul_pow, Real.sq_sqrt hp.le]
    ring
  have hratio := capacity_ratio k j hk
  have hratio' := mul_le_mul_of_nonneg_right hratio (show 0 ≤ ε ^ 2 * (delta (point k j : ℝ)) ^ 2 by positivity)
  have hbudget := hδ (point k j) (point_lower k j) (point_upper k j (by omega))
  have hbudget' := mul_le_mul_of_nonneg_left hbudget (show 0 ≤ ε ^ 2 / 4 by positivity)
  have hexponent : ε ^ 2 / 4 * Real.exp (exponent k / 2) ≤ (threshold ε k j) ^ 2 / (2 * (capacity k : ℝ)) := by
    apply hbudget'.trans
    rw [hsq]
    apply (le_div_iff₀ (by positivity : 0 < 2 * (capacity k : ℝ))).mpr
    nlinarith only [hratio']
  apply hprob.trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div]
  nlinarith only [hexponent]

theorem ae_eventual_cell_increment {ε : ℝ} (heps : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ j, j < count k → ∀ n, point k j ≤ n → n ≤ point k (j + 1) →
      |fullNorm ω n - fullNorm ω (point k j)| ≤ ε * normalizer (point k j : ℝ) := by
  have hsum : Summable (fun k : ℕ ↦ 8 / (k + 2 : ℝ) ^ 3) := by
    have h := (summable_nat_add_iff 2).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (3 : ℕ)))
    simpa only [Nat.cast_add, Nat.cast_ofNat, mul_one_div] using h.mul_left 8
  have hprobs : Summable (fun k ↦ P.real (badEvent ε k)) := by
    apply hsum.of_norm_bounded_eventually_nat
    filter_upwards [eventually_one_increment_bound heps,
      eventually_increment_probability_budget (show 0 < ε ^ 2 / 4 by positivity)] with k hone hbudget
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have hu := measureReal_iUnion_fintype_le (μ := P)
      (fun j : Fin (count k) ↦ {ω | ∃ n, point k j ≤ n ∧ n ≤ point k (j.val + 1) ∧
        threshold ε k j ≤ |fullNorm ω n - fullNorm ω (point k j)|})
    apply hu.trans
    have hsumle := Finset.sum_le_sum (fun (j : Fin (count k)) (_ : j ∈ Finset.univ) ↦ hone j j.isLt)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsumle
    have he : (count k : ℝ) * (4 * Real.exp (-(ε ^ 2 / 4) * Real.exp (exponent k / 2))) =
      4 * (count k : ℝ) * Real.exp (-(ε ^ 2 / 4) * Real.exp (exponent k / 2)) := by ring
    rw [he] at hsumle
    exact hsumle.trans hbudget
  have hfinite : (∑' k, P (badEvent ε k)) ≠ ⊤ := by
    have h := hprobs.tsum_ofReal_lt_top
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top P _)] at h
    exact ne_of_lt h
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with k hk
  intro j hj n hnj hnj1
  apply (lt_of_not_ge ?_).le
  intro hbad
  exact hk (Set.mem_iUnion.mpr ⟨⟨j, hj⟩, n, hnj, hnj1, hbad⟩)

end Erdos524.DenseMeshIncrement
