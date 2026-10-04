import Erdos524.PolynomialUpperError
import Erdos524.PolynomialInverseLower

/-! Actual inverse-scale full-polynomial upper probabilities, with every finite-comparison input discharged. -/

namespace Erdos524.PolynomialInverseUpper

open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open Erdos524.PolynomialComparisonParameters Erdos524.InversePolynomialScale
open Erdos524.FiniteSmallBallBasic Erdos524.RandomPolynomialModel
open Erdos524.PolynomialFullUpper Erdos524.PolynomialGridCover
open Erdos524.PolynomialInverseLower

noncomputable def upperBudget (c a D : ℝ) (N : ℕ) : ℝ :=
  Real.exp (-c * Real.sqrt (Real.log (Real.log (N : ℝ)))) / Real.log (N : ℝ) +
    D * Real.exp (-a * Real.log (N : ℝ))

theorem eventual_full_upper_budget {ε : ℝ} (heps : 0 < ε) (heps2 : ε < 1 / 2) :
    ∃ c D : ℝ, 0 < c ∧ 0 ≤ D ∧ ∀ᶠ N : ℕ in atTop, Even N →
      P.real {ω | fullNorm ω N ≤ (1 - ε) * normalizer (N : ℝ)} ≤ upperBudget c (1 / 16) D N := by
  obtain ⟨C, hC1, hcut⟩ := Erdos524.SmoothCutoff.exists_cutoff_derivative_bound
  have hC : 0 ≤ C := by linarith
  obtain ⟨c, hc, hmargin⟩ := eventually_squared_probability_margins
    (show 0 < ε / 2 by linarith) (show ε / 2 < 1 / 2 by linarith)
  refine ⟨c, 51200 * C + 114 + upperGridConstant, hc, ?_, ?_⟩
  · unfold upperGridConstant
    positivity
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
  have hr : 0 < (1 - ε) * delta ((2 * M : ℕ) : ℝ) := mul_pos (by linarith) hd
  have hshift : (1 - ε) * delta ((2 * M : ℕ) : ℝ) + 4 * tolerance (2 * M) ≤
      (1 - ε / 2) * delta ((2 * M : ℕ) : ℝ) := by nlinarith
  have hF := smallBallReal_mono hshift
  have hsq := (sq_le_sq₀ (show 0 ≤ smallBallReal ((1 - ε) * delta ((2 * M : ℕ) : ℝ) + 4 * tolerance (2 * M)) from ENNReal.toReal_nonneg)
    (show 0 ≤ smallBallReal ((1 - ε / 2) * delta ((2 * M : ℕ) : ℝ)) from ENNReal.toReal_nonneg)).mpr hF
  have hfull := full_polynomial_probability_upper (T := cutoffRange (2 * M)) hM hη
    (show 0 < (1 - ε) * delta ((2 * M : ℕ) : ℝ) + 4 * tolerance (2 * M) by positivity)
    (parameter_controls hN).2.2.2 hC (by simpa only [Nat.cast_add] using softBudget_log hN) hcut
  have hgrid := upperGridError_bound hN hr.le
  have hlaw : P.real {ω | fullNorm ω (2 * M) ≤ (1 - ε) * normalizer ((2 * M : ℕ) : ℝ)} =
      (Measure.pi (fun _ : Fin (2 * M) ↦ Erdos524.SignGaussianMoments.signLaw)).real
        (Erdos524.FullPolynomialBox.fullBox (2 * M) ((1 - ε) * delta ((2 * M : ℕ) : ℝ))) := by
    have hevent : {ω : Ω | fullNorm ω (2 * M) ≤ (1 - ε) * normalizer ((2 * M : ℕ) : ℝ)} =
        {ω | fullNorm ω (2 * M) ≤ Real.sqrt ((2 * M : ℕ) : ℝ) * ((1 - ε) * delta ((2 * M : ℕ) : ℝ))} := by
      ext ω
      congr 1
      unfold normalizer
      ring
    rw [hevent]
    exact fullNorm_scaled_probability hNp hr.le
  rw [hlaw]
  have heError := even_comparison_error_identity M C
  have htail : 0 ≤ 18 / (tolerance (2 * M) * Real.sqrt (cutoffRange (2 * M))) := by positivity
  have hcombined : (Measure.pi (fun _ : Fin (2 * M) ↦ Erdos524.SignGaussianMoments.signLaw)).real
        (Erdos524.FullPolynomialBox.fullBox (2 * M) ((1 - ε) * delta ((2 * M : ℕ) : ℝ))) ≤
      (smallBallReal ((1 - ε / 2) * delta ((2 * M : ℕ) : ℝ))) ^ 2 + comparisonError (2 * M) C +
        upperGridConstant * tolerance (2 * M) := by
    unfold upperGridError at hgrid
    rw [heError]
    linarith only [hfull, hsq, hgrid, htail]
  have hexp : Real.exp (-(1 / 16 : ℝ) * Real.log ((2 * M : ℕ) : ℝ)) =
      Real.exp (-Real.log ((2 * M : ℕ) : ℝ) / 16) := by congr 1; ring
  unfold upperBudget
  rw [hexp]
  dsimp only [tolerance] at hcombined
  nlinarith only [hmargin.2, hcombined, herr]

end Erdos524.PolynomialInverseUpper
