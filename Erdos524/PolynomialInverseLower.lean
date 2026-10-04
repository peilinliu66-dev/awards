import Erdos524.PolynomialTolerance
import Erdos524.InverseScaleProbabilityMargin
import Erdos524.RandomPolynomialBoxLaw
import Erdos524.SparseBlockBorelCantelli

/-! Actual full-polynomial lower probabilities and infinitely many independent small fresh blocks. -/

namespace Erdos524.PolynomialInverseLower

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open Erdos524.PolynomialComparisonParameters Erdos524.InversePolynomialScale
open Erdos524.InverseSmallBallMargins Erdos524.FiniteSmallBallBasic
open Erdos524.RandomPolynomialModel Erdos524.PolynomialFullProbability
open Erdos524.PolynomialGridCover Erdos524.SparseBlockBorelCantelli
open Erdos524.FactorialSparseMesh

theorem even_comparison_error_identity (M : ℕ) (C : ℝ) :
    comparisonError (2 * M) C =
      ((75 / 6 : ℝ) * C * (softBudget (2 * M)) ^ 3) / ((tolerance (2 * M)) ^ 4 * (2 * (M : ℝ))) +
        2 * (∑ j : Fin (gridCount (2 * M) (cutoffRange (2 * M))),
          (gridParameter (2 * M) (cutoffRange (2 * M)) j) ^ 2) / ((M : ℝ) ^ 2 * (tolerance (2 * M)) ^ 2) +
        18 / (tolerance (2 * M) * Real.sqrt (cutoffRange (2 * M))) := by
  unfold comparisonError
  push_cast
  simp only [mul_pow, div_eq_mul_inv, _root_.mul_inv_rev, inv_pow]
  ring

theorem eventual_full_lower_budget {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c D : ℝ, 0 < c ∧ 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      lowerBudget c (1 / 16) D N ≤ P.real {ω | fullNorm ω N ≤ (1 + ε) * normalizer (N : ℝ)} := by
  obtain ⟨C, hC1, hcut⟩ := Erdos524.SmoothCutoff.exists_cutoff_derivative_bound
  have hC : 0 ≤ C := by linarith
  obtain ⟨c, hc, hmargin⟩ := eventually_squared_probability_margins
    (show 0 < ε / 2 by linarith) (show ε / 2 < 1 / 2 by linarith)
  refine ⟨c, 51200 * C + 114, hc, by positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_comparison_error hC,
    eventually_tolerance_le_delta (show 0 < ε / 8 by linarith),
    tendsto_natCast_atTop_atTop.eventually hmargin,
    eventually_ge_atTop (1 : ℕ), hlog.eventually_gt_atTop (1 : ℝ)] with N herr htol hmargin hN hlogN
  intro hEven
  obtain ⟨M, he⟩ := hEven
  have he' : N = 2 * M := by omega
  clear he
  subst N
  have hM : 0 < M := by omega
  have hNp : 0 < 2 * M := by omega
  have hd : 0 < delta ((2 * M : ℕ) : ℝ) := delta_pos hlogN
  have hη := (parameter_controls hN).2.2.1
  have hT : 0 < cutoffRange (2 * M) := Real.exp_pos _
  have hr : 0 < (1 + ε) * delta ((2 * M : ℕ) : ℝ) := by positivity
  have hηr : tolerance (2 * M) ≤ (1 + ε) * delta ((2 * M : ℕ) : ℝ) := by nlinarith
  have hsqrt := inverse_sqrt_le_tolerance hN
  have hshift : (1 + ε / 2) * delta ((2 * M : ℕ) : ℝ) ≤
      (1 + ε) * delta ((2 * M : ℕ) : ℝ) - 1 / Real.sqrt ((2 * M : ℕ) : ℝ) - 3 * tolerance (2 * M) := by nlinarith
  have hF := smallBallReal_mono hshift
  have hsq := (sq_le_sq₀ (show 0 ≤ smallBallReal ((1 + ε / 2) * delta ((2 * M : ℕ) : ℝ)) from ENNReal.toReal_nonneg)
    (show 0 ≤ smallBallReal ((1 + ε) * delta ((2 * M : ℕ) : ℝ) - 1 / Real.sqrt ((2 * M : ℕ) : ℝ) - 3 * tolerance (2 * M)) from ENNReal.toReal_nonneg)).mpr hF
  have hfull := full_polynomial_probability_lower hM hT (parameter_controls hN).2.1 hη hηr
    (parameter_controls hN).2.2.2 hC (by simpa only [Nat.cast_add] using softBudget_log hN) hcut
  have hlaw : P.real {ω | fullNorm ω (2 * M) ≤ (1 + ε) * normalizer ((2 * M : ℕ) : ℝ)} =
      (Measure.pi (fun _ : Fin (2 * M) ↦ Erdos524.SignGaussianMoments.signLaw)).real
        (Erdos524.FullPolynomialBox.fullBox (2 * M) ((1 + ε) * delta ((2 * M : ℕ) : ℝ))) := by
    have hevent : {ω : Ω | fullNorm ω (2 * M) ≤ (1 + ε) * normalizer ((2 * M : ℕ) : ℝ)} =
        {ω | fullNorm ω (2 * M) ≤ Real.sqrt ((2 * M : ℕ) : ℝ) * ((1 + ε) * delta ((2 * M : ℕ) : ℝ))} := by
      ext ω
      congr 1
      unfold normalizer
      ring
    rw [hevent]
    exact fullNorm_scaled_probability hNp hr.le
  rw [hlaw]
  have heError := even_comparison_error_identity M C
  have hb : (smallBallReal ((1 + ε / 2) * delta ((2 * M : ℕ) : ℝ))) ^ 2 - comparisonError (2 * M) C ≤
      (Measure.pi (fun _ : Fin (2 * M) ↦ Erdos524.SignGaussianMoments.signLaw)).real
        (Erdos524.FullPolynomialBox.fullBox (2 * M) ((1 + ε) * delta ((2 * M : ℕ) : ℝ))) := by
    rw [heError]
    linarith only [hfull, hsq]
  have hexp : Real.exp (-(1 / 16 : ℝ) * Real.log ((2 * M : ℕ) : ℝ)) =
      Real.exp (-Real.log ((2 * M : ℕ) : ℝ) / 16) := by congr 1; ring
  unfold lowerBudget
  rw [hexp]
  linarith only [hmargin.1, hb, herr]

theorem ae_frequent_actual_fresh_small {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∀ᵐ ω ∂P, ∃ᶠ j in atTop,
      freshNorm (endpoint j) (blockLength j) ω ≤ (1 + ε) * normalizer (blockLength j : ℝ) := by
  obtain ⟨c, D, hc, hD, hp⟩ := eventual_full_lower_budget heps heps2
  exact ae_frequent_fresh_small_of_budget hc (by norm_num : (0 : ℝ) < 1 / 16) hD hp

end Erdos524.PolynomialInverseLower
