import Erdos524.DenseMeshIncrement
import Erdos524.InversePolynomialScale

/-! The exact inverse normalization changes negligibly within each adaptive dyadic cell. -/

namespace Erdos524.AdaptiveDyadicMesh

open Filter
open Erdos524.InversePolynomialScale

theorem normalizer_le_of_relative_degree {A N ε : ℝ} (hA : 0 < A) (hlogA : 1 < Real.log A)
    (heps : 0 < ε) (hAN : A ≤ N) (hrel : N ≤ (1 + ε) ^ 2 * A) :
    normalizer N ≤ (1 + ε) * normalizer A := by
  have hδ := delta_antitone hA hlogA hAN
  have hsA := Real.sq_sqrt hA.le
  have hNp : 0 < N := hA.trans_le hAN
  have hsN := Real.sq_sqrt hNp.le
  have hroot : Real.sqrt N ≤ (1 + ε) * Real.sqrt A := by
    have hsq : (Real.sqrt N) ^ 2 ≤ ((1 + ε) * Real.sqrt A) ^ 2 := by rw [mul_pow, hsA, hsN]; exact hrel
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp hsq
  unfold normalizer
  calc
    _ ≤ ((1 + ε) * Real.sqrt A) * delta A := mul_le_mul hroot hδ (delta_nonneg _) (by positivity)
    _ = _ := by ring

theorem eventually_cell_normalizer {ε : ℝ} (heps : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ j, j < count k → ∀ n, point k j ≤ n → n ≤ point k (j + 1) →
      normalizer (n : ℝ) ≤ (1 + ε) * normalizer (point k j : ℝ) := by
  have hb : Tendsto (fun k : ℕ ↦ Real.log ((2 * 2 ^ k : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp Erdos524.DyadicMesh.base_tendsto_atTop)
  filter_upwards [eventually_count_le_dyadic, count_real_tendsto.eventually_ge_atTop (2 / ε),
    hb.eventually_gt_atTop (1 : ℝ)] with k hk hQlarge hlogbase
  intro j hj n hnj hnj1
  have hApos : (0 : ℝ) < point k j := by
    have hp := point_lower k j
    have hpow : 0 < 2 ^ k := pow_pos (by norm_num) _
    exact_mod_cast (show 0 < point k j by omega)
  have hlogA : 1 < Real.log (point k j : ℝ) :=
    hlogbase.trans_le (Real.log_le_log (by positivity) (by exact_mod_cast point_lower k j))
  have hQp : (0 : ℝ) < count k := by exact_mod_cast count_pos k
  have hfrac : 2 / (count k : ℝ) ≤ ε := by
    apply (div_le_iff₀ hQp).mpr
    have hh := (div_le_iff₀ heps).mp hQlarge
    nlinarith
  have hstep := Erdos524.DyadicMesh.point_step_ratio k (count k) j (count_pos k) hk
  change (point k (j + 1) : ℝ) ≤ (1 + 2 / (count k : ℝ)) * (point k j : ℝ) at hstep
  have hn : (n : ℝ) ≤ point k (j + 1) := by exact_mod_cast hnj1
  apply normalizer_le_of_relative_degree hApos hlogA heps (by exact_mod_cast hnj)
  have hmul := mul_le_mul_of_nonneg_right hfrac hApos.le
  have hslack : (1 + ε) * (point k j : ℝ) ≤ (1 + ε) ^ 2 * (point k j : ℝ) := by
    have hh := mul_nonneg (show 0 ≤ ε * (1 + ε) by positivity) hApos.le
    nlinarith only [hh]
  nlinarith only [hn, hstep, hmul, hslack]

end Erdos524.AdaptiveDyadicMesh
