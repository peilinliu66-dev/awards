import Erdos524.PolynomialInverseLower
import Erdos524.FactorialOldPayment

/-! The sparse-block direction of the exact inverse-normalized liminf, for the actual sign polynomial. -/

namespace Erdos524.InverseLiminfUpper

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.RandomPolynomialModel Erdos524.InversePolynomialScale
open Erdos524.PolynomialInverseLower Erdos524.SparseBlockBorelCantelli
open Erdos524.FactorialSparseMesh

theorem ae_frequent_full_small {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ᶠ N in atTop, fullNorm ω N ≤ (1 + ε) * normalizer (N : ℝ) := by
  have he4 : 0 < ε / 4 := by linarith
  have he42 : ε / 4 < 1 / 2 := by linarith
  obtain ⟨c, D, hc, hD, hp⟩ := eventual_full_lower_budget he4 he42
  apply ae_frequent_full_small_of_budget_and_old hc (by norm_num : (0 : ℝ) < 1 / 16) hD hp oldBudget ae_eventual_old_bound
  filter_upwards [eventually_old_payment he4, eventually_block_normalizer_le he4 he42] with j hold hscale
  have hconst : (1 + ε / 4) ^ 2 + ε / 4 ≤ 1 + ε := by nlinarith
  calc
    _ ≤ (1 + ε / 4) * ((1 + ε / 4) * normalizer (endpoint (j + 1) : ℝ)) +
        ε / 4 * normalizer (endpoint (j + 1) : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hscale (by positivity)) hold
    _ = ((1 + ε / 4) ^ 2 + ε / 4) * normalizer (endpoint (j + 1) : ℝ) := by ring
    _ ≤ (1 + ε) * normalizer (endpoint (j + 1) : ℝ) :=
      mul_le_mul_of_nonneg_right hconst (normalizer_nonneg _)

theorem eventually_normalizer_pos : ∀ᶠ N : ℕ in atTop, 0 < normalizer (N : ℝ) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop (1 : ℝ), eventually_ge_atTop (1 : ℕ)] with N hlogN hN
  unfold normalizer
  exact mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast lt_of_lt_of_le (by decide : 0 < 1) hN)) (delta_pos hlogN)

theorem ae_frequent_ratio_le {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ᶠ N in atTop, fullNorm ω N / normalizer (N : ℝ) ≤ 1 + ε := by
  filter_upwards [ae_frequent_full_small heps heps2] with ω hω
  apply (hω.and_eventually eventually_normalizer_pos).mono
  intro N hN
  exact (div_le_iff₀ hN.2).mpr hN.1

theorem ae_frequent_ratio_all_positive_slack :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ᶠ N in atTop, fullNorm ω N / normalizer (N : ℝ) ≤ 1 + ε := by
  have hcount : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ᶠ N in atTop,
      fullNorm ω N / normalizer (N : ℝ) ≤ 1 + 1 / (k + 3 : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_frequent_ratio_le (by positivity)
    apply (div_lt_iff₀ (by positivity : 0 < (k + 3 : ℝ))).mpr
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  filter_upwards [hcount] with ω hω
  intro ε heps
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  have hkpos : (0 : ℝ) < k + 3 := by positivity
  have hsmall : 1 / (k + 3 : ℝ) ≤ ε := by
    apply (div_le_iff₀ hkpos).mpr
    have h := (div_lt_iff₀ heps).mp hk
    nlinarith
  exact (hω k).mono (fun N hN ↦ hN.trans (by linarith))

theorem ae_inverse_normalized_liminf_le_one :
    ∀ᵐ ω ∂P, liminf (fun N ↦ fullNorm ω N / normalizer (N : ℝ)) atTop ≤ 1 := by
  filter_upwards [ae_frequent_ratio_all_positive_slack] with ω hω
  have hb : IsBoundedUnder (fun x y : ℝ ↦ y ≤ x) atTop
      (fun N ↦ fullNorm ω N / normalizer (N : ℝ)) :=
    isBoundedUnder_of ⟨0, fun N ↦ div_nonneg (fullNorm_nonneg ω N) (normalizer_nonneg _)⟩
  apply le_of_forall_pos_le_add
  intro ε heps
  exact liminf_le_of_frequently_le (hω ε heps) hb

end Erdos524.InverseLiminfUpper
