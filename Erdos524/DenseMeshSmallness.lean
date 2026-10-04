import Erdos524.AdaptiveDyadicMesh
import Erdos524.DyadicLogBounds
import Erdos524.StretchedLogSummability
import Erdos524.PolynomialInverseUpper

/-! Summable smallness probabilities on the actual adaptive even dyadic mesh. -/

namespace Erdos524.DenseMeshSmallness

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Erdos524.AdaptiveDyadicMesh Erdos524.RandomPolynomialModel
open Erdos524.InversePolynomialScale Erdos524.PolynomialInverseUpper
open Erdos524.StretchedLogSummability

noncomputable def bandBudget (c a D : ℝ) (k : ℕ) : ℝ :=
  12 * Real.exp (-(c / 4) * Real.sqrt (Real.log (k + 2 : ℝ))) / (k + 2 : ℝ) +
    2 * D * (k + 2 : ℝ) * Real.exp (-a * (k + 2 : ℝ) / 4)

noncomputable def badEvent (ε : ℝ) (k : ℕ) : Set Ω :=
  ⋃ j : Fin (count k + 1), {ω | fullNorm ω (point k j) ≤ (1 - ε) * normalizer (point k j : ℝ)}

theorem summable_bandBudget {c a D : ℝ} (hc : 0 < c) (ha : 0 < a) : Summable (bandBudget c a D) := by
  have h1 := (summable_shifted_stretched_log_harmonic (show 0 < c / 4 by positivity) 2).mul_left 12
  have h2 := (summable_nat_add_iff 2).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul 1 (show 0 < a / 4 by positivity))
  have h2' := h2.mul_left (2 * D)
  convert h1.add h2' using 1
  funext k
  unfold bandBudget
  push_cast
  simp only [pow_one]
  rw [show -a * (k + 2 : ℝ) / 4 = -(a / 4) * (k + 2 : ℝ) by ring]
  ring

theorem eventually_count_upperBudget {c a D : ℝ} (hc : 0 < c) (ha : 0 < a) (hD : 0 ≤ D) :
    ∀ᶠ k : ℕ in atTop, ∀ N : ℕ, 2 * 2 ^ k ≤ N → N ≤ 4 * 2 ^ k →
      ((count k + 1 : ℕ) : ℝ) * upperBudget c a D N ≤ bandBudget c a D k := by
  filter_upwards [Erdos524.DyadicMesh.eventually_sqrt_loglog_band_lower,
    eventually_exponent_le_sqrt (show 0 < c / 4 by positivity), eventually_count_le_index] with k hs hu hcount
  intro N hlo hhi
  let J : ℝ := k + 2
  let z : ℝ := Real.log (N : ℝ)
  have hJ : 0 < J := by unfold J; positivity
  have hJ1 : 1 ≤ J := by unfold J; have hh : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
  have hb := Erdos524.DyadicMesh.band_log_bounds hlo hhi
  have hz : 0 < z := lt_of_lt_of_le (by positivity) hb.1
  have hroot := hs N hlo hhi
  have hmain : Real.exp (-c * Real.sqrt (Real.log z)) / z ≤
      4 * Real.exp (-(c / 2) * Real.sqrt (Real.log J)) / J := by
    have hn : Real.exp (-c * Real.sqrt (Real.log z)) ≤
        Real.exp (-(c / 2) * Real.sqrt (Real.log J)) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hroot hc.le]
    have hh := div_le_div₀ (Real.exp_pos _).le hn (show 0 < J / 4 by positivity) hb.1
    convert hh using 1 <;> ring
  have herr : D * Real.exp (-a * z) ≤ D * Real.exp (-a * J / 4) := by
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD
    have hh := mul_le_mul_of_nonneg_left hb.1 ha.le
    dsimp only [z, J] at *
    linarith
  have hcount1 : ((count k + 1 : ℕ) : ℝ) ≤ 3 * Real.exp (exponent k) := by
    have hh := (count_bounds k).2
    have he := Real.one_le_exp_iff.mpr (exponent_nonneg k)
    push_cast
    linarith
  have hcount2 : ((count k + 1 : ℕ) : ℝ) ≤ 2 * J := by
    have hh : (count k : ℝ) ≤ J := by dsimp only [J]; exact_mod_cast hcount
    push_cast
    linarith
  have hfirst := mul_le_mul hcount1 hmain (by positivity : 0 ≤ Real.exp (-c * Real.sqrt (Real.log z)) / z) (by positivity)
  have hsecond := mul_le_mul hcount2 herr (by positivity : 0 ≤ D * Real.exp (-a * z)) (by positivity)
  have he : 3 * Real.exp (exponent k) * (4 * Real.exp (-(c / 2) * Real.sqrt (Real.log J)) / J) =
      12 * Real.exp (exponent k - (c / 2) * Real.sqrt (Real.log J)) / J := by
    calc
      _ = 12 * (Real.exp (exponent k) * Real.exp (-(c / 2) * Real.sqrt (Real.log J))) / J := by ring
      _ = _ := by
        rw [← Real.exp_add]
        congr 2
        ring
  rw [he] at hfirst
  have hdec : Real.exp (exponent k - (c / 2) * Real.sqrt (Real.log J)) ≤
      Real.exp (-(c / 4) * Real.sqrt (Real.log J)) := Real.exp_le_exp.mpr (by dsimp only [J]; linarith)
  have hfirst' := hfirst.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdec (by norm_num)) hJ.le)
  unfold upperBudget bandBudget
  change ((count k + 1 : ℕ) : ℝ) * (Real.exp (-c * Real.sqrt (Real.log z)) / z + D * Real.exp (-a * z)) ≤
    12 * Real.exp (-(c / 4) * Real.sqrt (Real.log J)) / J + 2 * D * J * Real.exp (-a * J / 4)
  nlinarith only [hfirst', hsecond]

theorem ae_eventual_mesh_large {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ j, j ≤ count k →
      (1 - ε) * normalizer (point k j : ℝ) < fullNorm ω (point k j) := by
  obtain ⟨c, D, hc, hD, hp⟩ := eventual_full_upper_budget heps heps2
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp hp
  have hsum := summable_bandBudget (D := D) hc (by norm_num : (0 : ℝ) < 1 / 16)
  have hsP : Summable (fun k ↦ P.real (badEvent ε k)) := by
    apply hsum.of_norm_bounded_eventually_nat
    filter_upwards [eventually_count_upperBudget hc (by norm_num : (0 : ℝ) < 1 / 16) hD,
      Erdos524.DyadicMesh.base_tendsto_atTop.eventually_ge_atTop N0] with k hbudget hk
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    have hu := measureReal_iUnion_fintype_le (μ := P)
      (fun j : Fin (count k + 1) ↦ {ω | fullNorm ω (point k j) ≤ (1 - ε) * normalizer (point k j : ℝ)})
    apply hu.trans
    have hcpos : (0 : ℝ) < (count k + 1 : ℕ) := by positivity
    have hone (j : Fin (count k + 1)) :
        P.real {ω | fullNorm ω (point k j) ≤ (1 - ε) * normalizer (point k j : ℝ)} ≤
          bandBudget c (1 / 16) D k / ((count k + 1 : ℕ) : ℝ) := by
      have hj : j.val ≤ count k := by omega
      have hb := hbudget (point k j) (point_lower k j) (point_upper k j hj)
      have hactual := hN0 (point k j) (hk.trans (point_lower k j)) (point_even k j)
      apply hactual.trans
      apply (le_div_iff₀ hcpos).mpr
      nlinarith only [hb]
    calc
      _ ≤ ∑ _j : Fin (count k + 1), bandBudget c (1 / 16) D k / ((count k + 1 : ℕ) : ℝ) :=
        Finset.sum_le_sum (fun j _ ↦ hone j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  have hfinite : (∑' k, P (badEvent ε k)) ≠ ⊤ := by
    have h := hsP.tsum_ofReal_lt_top
    simp only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top P _)] at h
    exact ne_of_lt h
  filter_upwards [ae_eventually_notMem hfinite] with ω hω
  filter_upwards [hω] with k hk
  intro j hj
  apply lt_of_not_ge
  intro hbad
  exact hk (Set.mem_iUnion.mpr ⟨⟨j, by omega⟩, hbad⟩)

end Erdos524.DenseMeshSmallness
