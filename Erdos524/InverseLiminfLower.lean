import Erdos524.DenseMeshSmallness
import Erdos524.DenseScaleComparison
import Erdos524.InverseLiminfUpper

/-! The dense all-sequence direction of the exact inverse-normalized liminf. -/

namespace Erdos524.InverseLiminfLower

open Set Filter MeasureTheory ProbabilityTheory
open Erdos524.AdaptiveDyadicMesh Erdos524.RandomPolynomialModel
open Erdos524.InversePolynomialScale Erdos524.DenseMeshSmallness Erdos524.DenseMeshIncrement

theorem ae_eventual_full_large {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ε) * normalizer (N : ℝ) ≤ fullNorm ω N := by
  have he4 : 0 < ε / 4 := by linarith
  have he42 : ε / 4 < 1 / 2 := by linarith
  filter_upwards [ae_eventual_mesh_large he4 he42, ae_eventual_cell_increment he4] with ω hlarge hinc
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((hlarge.and hinc).and (eventually_cell_normalizer he4))
  filter_upwards [eventually_ge_atTop (4 * 2 ^ K)] with n hn
  obtain ⟨k, hk, j, hj, hnj, hnj1⟩ := Erdos524.DyadicMesh.cover_after count count_pos K n hn
  have h := hK k hk
  have hA := h.1.1 j hj.le
  have hI := (abs_le.mp (h.1.2 j hj n hnj hnj1.le)).1
  have hS := h.2 j hj n hnj hnj1.le
  have hM : (1 - ε / 2) * normalizer (point k j : ℝ) ≤ fullNorm ω n := by nlinarith only [hA, hI]
  have hconst : (1 - ε) * (1 + ε / 4) ≤ 1 - ε / 2 := by nlinarith
  calc
    _ ≤ (1 - ε) * ((1 + ε / 4) * normalizer (point k j : ℝ)) :=
      mul_le_mul_of_nonneg_left hS (by linarith)
    _ = ((1 - ε) * (1 + ε / 4)) * normalizer (point k j : ℝ) := by ring
    _ ≤ (1 - ε / 2) * normalizer (point k j : ℝ) :=
      mul_le_mul_of_nonneg_right hconst (normalizer_nonneg _)
    _ ≤ fullNorm ω n := hM

theorem ae_eventual_ratio_ge {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, 1 - ε ≤ fullNorm ω N / normalizer (N : ℝ) := by
  filter_upwards [ae_eventual_full_large heps heps2] with ω hω
  filter_upwards [hω, Erdos524.InverseLiminfUpper.eventually_normalizer_pos] with N hN hb
  exact (le_div_iff₀ hb).mpr hN

theorem ae_eventual_ratio_all_positive_slack :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, 1 - ε ≤ fullNorm ω N / normalizer (N : ℝ) := by
  have hcount : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ N : ℕ in atTop,
      1 - 1 / (k + 3 : ℝ) ≤ fullNorm ω N / normalizer (N : ℝ) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_eventual_ratio_ge (by positivity)
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
  exact (hω k).mono (fun N hN ↦ le_trans (by linarith) hN)

theorem ae_inverse_normalized_liminf_ge_one :
    ∀ᵐ ω ∂P, 1 ≤ liminf (fun N ↦ fullNorm ω N / normalizer (N : ℝ)) atTop := by
  filter_upwards [ae_eventual_ratio_all_positive_slack,
    Erdos524.InverseLiminfUpper.ae_frequent_ratio_le (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1 / 2)] with ω hω hu
  have hbound : IsCoboundedUnder (fun x y : ℝ ↦ y ≤ x) atTop
      (fun N ↦ fullNorm ω N / normalizer (N : ℝ)) := IsCoboundedUnder.of_frequently_le hu
  apply le_of_forall_pos_sub_le
  intro ε heps
  exact le_liminf_of_le hbound (hω ε heps)

end Erdos524.InverseLiminfLower
